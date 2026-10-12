//! Property tests: resolve-lang against a simple reference resolver on
//! random scoped programs, plus the DIRECTIVES §4 invariants (one binder or
//! one diagnostic per reference, determinism and order independence under
//! hoisting, index consistency).
//!
//! The programs include the HIR 0.4 forms: `let_place` aliases (visible in
//! their body only, crossing no frame), keyed `yield` and `yield from`
//! operands, and type annotations built from unions, intersections, and
//! nullable members over generic parameters, which hir-lang normalizes
//! (sorts, flattens, drops repeats) before the resolver sees them.

// Test models are small tuple-heavy trees; naming every tuple type would
// only add noise.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::type_complexity)]

use hir_lang::{
    Binder, BinderKind, Builder, CaptureMode, Closure, Def, DefId, Effects, Expr, ExprId, FnDef,
    GenericParam, Generics, Hir, Item, ItemId, ItemKind, Name, NodeRef, Ns, Param, Path, PathId,
    Res, Segment, Span, Stmt, StmtId, Ty, TyId, UnitId,
};
use intern_lang::Interner;
use proptest::prelude::*;
use resolve_lang::{Hoist, ItemClass, Policy, Resolution, Resolver};

// ------------------------------------------------------------------ model

#[derive(Clone, Debug)]
enum E {
    Use(u8),
    Block(Vec<S>, Option<Box<E>>),
    Closure(Vec<u8>, Box<E>),
    Tuple(Vec<E>),
    /// `yield`, `yield v`, or `yield k => v` (a key needs a value).
    Yield(Option<(Option<Box<E>>, Box<E>)>),
    YieldFrom(Box<E>),
    /// `let_place n = base[index] in body`.
    LetPlace(u8, u8, Box<E>, Box<E>),
}

/// A type annotation: names (generic parameters, or nothing), and the
/// union, intersection, and nullable forms hir-lang normalizes.
#[derive(Clone, Debug)]
enum T {
    Name(u8),
    Nullable(u8),
    Union(Vec<T>),
    Inter(Vec<T>),
}

#[derive(Clone, Debug)]
enum S {
    Let(u8, Option<T>, Option<E>),
    Fn(F),
    Expr(E),
}

/// `fn name<tps>(ps) yield { body; tail }`.
#[derive(Clone, Debug)]
struct F {
    name: u8,
    tps: Vec<u8>,
    ps: Vec<u8>,
    body: Vec<S>,
    tail: Option<E>,
}

#[derive(Clone, Debug)]
struct Prog {
    items: Vec<F>,
}

const NAMES: [&str; 5] = ["a", "b", "c", "d", "e"];

/// Distinct generic parameter names (a repeated one is a HIR error).
fn tparams() -> impl Strategy<Value = Vec<u8>> {
    proptest::collection::vec(0u8..5, 0..3).prop_map(|mut v| {
        v.sort_unstable();
        v.dedup();
        v
    })
}

fn ty() -> impl Strategy<Value = T> {
    let leaf = prop_oneof![(0u8..5).prop_map(T::Name), (0u8..5).prop_map(T::Nullable)];
    leaf.prop_recursive(2, 12, 3, |inner| {
        prop_oneof![
            proptest::collection::vec(inner.clone(), 2..4).prop_map(T::Union),
            proptest::collection::vec(inner, 2..4).prop_map(T::Inter),
        ]
    })
}

fn let_stmt(inner: impl Strategy<Value = E>) -> impl Strategy<Value = S> {
    (
        0u8..5,
        proptest::option::of(ty()),
        proptest::option::of(inner),
    )
        .prop_map(|(n, t, e)| S::Let(n, t, e))
}

fn expr() -> impl Strategy<Value = E> {
    let leaf = (0u8..5).prop_map(E::Use);
    leaf.prop_recursive(5, 48, 4, |inner| {
        let stmt = prop_oneof![
            let_stmt(inner.clone()),
            (
                (0u8..5),
                tparams(),
                proptest::collection::vec(0u8..5, 0..2),
                proptest::collection::vec(let_stmt(inner.clone()), 0..3),
                proptest::option::of(inner.clone())
            )
                .prop_map(|(name, tps, ps, body, tail)| S::Fn(F {
                    name,
                    tps,
                    ps,
                    body,
                    tail
                })),
            inner.clone().prop_map(S::Expr),
        ];
        let boxed = inner.clone().prop_map(Box::new);
        prop_oneof![
            (
                proptest::collection::vec(stmt, 0..4),
                proptest::option::of(inner.clone())
            )
                .prop_map(|(s, t)| E::Block(s, t.map(Box::new))),
            (proptest::collection::vec(0u8..5, 0..2), boxed.clone())
                .prop_map(|(ps, b)| E::Closure(ps, b)),
            proptest::collection::vec(inner, 1..4).prop_map(E::Tuple),
            proptest::option::of((proptest::option::of(boxed.clone()), boxed.clone()))
                .prop_map(E::Yield),
            boxed.clone().prop_map(E::YieldFrom),
            ((0u8..5), (0u8..5), boxed.clone(), boxed)
                .prop_map(|(n, base, ix, body)| E::LetPlace(n, base, ix, body)),
        ]
    })
}

fn prog() -> impl Strategy<Value = Prog> {
    proptest::collection::vec(
        (
            0u8..5,
            tparams(),
            proptest::collection::vec(0u8..5, 0..3),
            proptest::collection::vec(expr().prop_map(S::Expr), 0..3),
            proptest::option::of(expr()),
        )
            .prop_map(|(name, tps, ps, body, tail)| F {
                name,
                tps,
                ps,
                body,
                tail,
            }),
        1..5,
    )
    .prop_map(|items| Prog { items })
}

// -------------------------------------------------------- reference resolver

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Expect {
    Local(usize),
    Item(usize),
    Err,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Module,
    Block,
    FnItem,
    Closure,
}

/// What a scope entry is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Entry {
    Item,
    /// A `let` or a parameter: crosses closures, not function items.
    Local,
    /// A `let_place` alias: crosses no frame at all.
    Place,
    /// A generic parameter: in the type namespace; crosses closures.
    TypeParam,
}

struct RScope {
    kind: Kind,
    /// (name, target, what, seq)
    entries: Vec<(u8, Expect, Entry, u64)>,
}

/// The obvious, slow resolver: a stack of scopes searched innermost-out.
struct Reference {
    scopes: Vec<RScope>,
    seq: u64,
    binders: usize,
    /// What each binder is, by binder index.
    kinds: Vec<Entry>,
    items: usize,
    uses: Vec<Expect>,
    after_decl: bool,
}

impl Reference {
    fn tick(&mut self) -> u64 {
        self.seq += 1;
        self.seq
    }

    /// A value name: the innermost item, local, or place alias. A local
    /// past a function item, or an alias past any frame, is an error.
    fn lookup(&self, n: u8) -> Expect {
        let (mut crossed_fn, mut crossed_frame) = (false, false);
        for scope in self.scopes.iter().rev() {
            let best = scope
                .entries
                .iter()
                .filter(|e| e.0 == n && e.2 != Entry::TypeParam)
                .max_by_key(|e| e.3);
            if let Some(&(_, target, what, _)) = best {
                let blocked = match what {
                    Entry::Local => crossed_fn,
                    Entry::Place => crossed_frame,
                    Entry::Item | Entry::TypeParam => false,
                };
                return if blocked { Expect::Err } else { target };
            }
            match scope.kind {
                Kind::FnItem => (crossed_fn, crossed_frame) = (true, true),
                Kind::Closure => crossed_frame = true,
                Kind::Module | Kind::Block => {}
            }
        }
        Expect::Err
    }

    /// A type name: only generic parameters are types here (the items are
    /// functions); one of an enclosing function item is out of reach.
    fn lookup_type(&self, n: u8) -> Expect {
        let mut crossed_fn = false;
        for scope in self.scopes.iter().rev() {
            if let Some(&(_, target, _, _)) = scope
                .entries
                .iter()
                .find(|e| e.0 == n && e.2 == Entry::TypeParam)
            {
                return if crossed_fn { Expect::Err } else { target };
            }
            if scope.kind == Kind::FnItem {
                crossed_fn = true;
            }
        }
        Expect::Err
    }

    fn ty(&mut self, t: &T) {
        match t {
            T::Name(n) | T::Nullable(n) => {
                let r = self.lookup_type(*n);
                self.uses.push(r);
            }
            T::Union(ts) | T::Inter(ts) => ts.iter().for_each(|t| self.ty(t)),
        }
    }

    fn push_item(&mut self, n: u8, idx: usize) {
        let seq = self.tick();
        let scope = self.scopes.last_mut().unwrap();
        // Duplicates: the first definition is kept.
        if !scope.entries.iter().any(|e| e.0 == n && e.2 == Entry::Item) {
            scope.entries.push((n, Expect::Item(idx), Entry::Item, seq));
        }
    }

    fn push_binder(&mut self, n: u8, what: Entry) {
        let idx = self.binders;
        self.binders += 1;
        self.kinds.push(what);
        let seq = self.tick();
        self.scopes
            .last_mut()
            .unwrap()
            .entries
            .push((n, Expect::Local(idx), what, seq));
    }

    fn open(&mut self, kind: Kind) {
        self.scopes.push(RScope {
            kind,
            entries: Vec::new(),
        });
    }

    fn expr(&mut self, e: &E) {
        match e {
            E::Use(n) => {
                let r = self.lookup(*n);
                self.uses.push(r);
            }
            E::Tuple(xs) => xs.iter().for_each(|x| self.expr(x)),
            E::Block(stmts, tail) => self.block(stmts, tail.as_deref()),
            E::Closure(ps, body) => {
                self.open(Kind::Closure);
                for p in ps {
                    self.push_binder(*p, Entry::Local);
                }
                self.expr(body);
                self.scopes.pop();
            }
            E::Yield(kv) => {
                if let Some((k, v)) = kv {
                    if let Some(k) = k {
                        self.expr(k);
                    }
                    self.expr(v);
                }
            }
            E::YieldFrom(x) => self.expr(x),
            E::LetPlace(n, base, ix, body) => {
                // The place's operands, in the outer scope; then the alias,
                // visible in the body only.
                let r = self.lookup(*base);
                self.uses.push(r);
                self.expr(ix);
                self.open(Kind::Block);
                self.push_binder(*n, Entry::Place);
                self.expr(body);
                self.scopes.pop();
            }
        }
    }

    /// Item indexes are assigned in preorder; with scope hoisting the names
    /// are pushed at scope open, so their indexes are reserved up front.
    fn block(&mut self, stmts: &[S], tail: Option<&E>) {
        self.open(Kind::Block);
        // Item indexes are preorder: each statement starts where the items
        // of the statements before it end.
        let mut starts = Vec::with_capacity(stmts.len());
        let mut idx = self.items;
        for s in stmts {
            starts.push(idx);
            idx += count_items_stmt(s);
        }
        if !self.after_decl {
            for (s, &i) in stmts.iter().zip(&starts) {
                if let S::Fn(f) = s {
                    self.push_item(f.name, i);
                }
            }
        }
        for (s, &i) in stmts.iter().zip(&starts) {
            self.items = i;
            match s {
                S::Let(n, t, init) => {
                    if let Some(t) = t {
                        self.ty(t);
                    }
                    if let Some(e) = init {
                        self.expr(e);
                    }
                    self.push_binder(*n, Entry::Local);
                }
                S::Expr(e) => self.expr(e),
                S::Fn(f) => {
                    if self.after_decl {
                        self.push_item(f.name, i);
                    }
                    self.items = i + 1;
                    self.func(f);
                }
            }
        }
        self.items = idx;
        if let Some(t) = tail {
            self.expr(t);
        }
        self.scopes.pop();
    }

    fn func(&mut self, f: &F) {
        self.open(Kind::FnItem);
        for t in &f.tps {
            self.push_binder(*t, Entry::TypeParam);
        }
        for p in &f.ps {
            self.push_binder(*p, Entry::Local);
        }
        self.block(&f.body, f.tail.as_ref());
        self.scopes.pop();
    }

    fn run_full(prog: &Prog, after_decl: bool) -> Self {
        let mut r = Reference {
            scopes: Vec::new(),
            seq: 0,
            binders: 0,
            kinds: Vec::new(),
            items: 0,
            uses: Vec::new(),
            after_decl,
        };
        r.open(Kind::Module);
        let mut reserved = Vec::new();
        let mut idx = 0;
        for it in &prog.items {
            reserved.push(idx);
            idx += 1 + count_items(&it.body, it.tail.as_ref());
        }
        if !after_decl {
            for (it, i) in prog.items.iter().zip(&reserved) {
                r.push_item(it.name, *i);
            }
        }
        for (it, i) in prog.items.iter().zip(&reserved) {
            if after_decl {
                r.push_item(it.name, *i);
            }
            r.items = i + 1;
            r.func(it);
        }
        r
    }

    fn run(prog: &Prog, after_decl: bool) -> Vec<Expect> {
        Self::run_full(prog, after_decl).uses
    }
}

fn count_items_stmt(s: &S) -> usize {
    match s {
        S::Fn(f) => 1 + count_items(&f.body, f.tail.as_ref()),
        S::Let(_, _, Some(e)) | S::Expr(e) => count_items_expr(e),
        S::Let(_, _, None) => 0,
    }
}

fn count_items(stmts: &[S], tail: Option<&E>) -> usize {
    stmts.iter().map(count_items_stmt).sum::<usize>() + tail.map_or(0, count_items_expr)
}

fn count_items_expr(e: &E) -> usize {
    match e {
        E::Use(_) | E::Yield(None) => 0,
        E::Tuple(xs) => xs.iter().map(count_items_expr).sum(),
        E::Block(s, t) => count_items(s, t.as_deref()),
        E::Closure(_, b) | E::YieldFrom(b) => count_items_expr(b),
        E::Yield(Some((k, v))) => k.as_deref().map_or(0, count_items_expr) + count_items_expr(v),
        E::LetPlace(_, _, ix, body) => count_items_expr(ix) + count_items_expr(body),
    }
}

// ------------------------------------------------------------- HIR builder

struct Build {
    b: Builder,
    names: [Name; 5],
    binders: Vec<hir_lang::BinderId>,
    items: Vec<Option<ItemId>>,
    uses: Vec<PathId>,
    pos: u32,
}

impl Build {
    fn span(&mut self) {
        self.pos += 2;
        self.b.set_span(Span::new(self.pos, self.pos + 1));
    }

    fn binder(&mut self, n: u8, kind: BinderKind) -> hir_lang::BinderId {
        self.span();
        let b = self.b.binder(Binder::new(self.names[n as usize], kind));
        self.binders.push(b);
        b
    }

    /// A one-segment path, recorded as a use.
    fn path(&mut self, n: u8, ns: Ns) -> PathId {
        self.span();
        let seg = Segment::new(self.names[n as usize], self.b.origin());
        let segs = self.b.list(&[seg]);
        let p = self.b.path(Path::new(segs, ns));
        self.uses.push(p);
        p
    }

    fn ty(&mut self, t: &T) -> TyId {
        match t {
            T::Name(n) => {
                let p = self.path(*n, Ns::Type);
                self.b.ty(Ty::Path(p))
            }
            T::Nullable(n) => {
                let p = self.path(*n, Ns::Type);
                let inner = self.b.ty(Ty::Path(p));
                self.b.ty(Ty::Nullable(inner))
            }
            T::Union(ts) | T::Inter(ts) => {
                let ids: Vec<TyId> = ts.iter().map(|t| self.ty(t)).collect();
                let l = self.b.list(&ids);
                self.b.ty(if matches!(t, T::Union(_)) {
                    Ty::Union(l)
                } else {
                    Ty::Intersection(l)
                })
            }
        }
    }

    fn expr(&mut self, e: &E) -> ExprId {
        match e {
            E::Use(n) => {
                let p = self.path(*n, Ns::Value);
                self.b.expr(Expr::Path(p))
            }
            E::Tuple(xs) => {
                let ids: Vec<ExprId> = xs.iter().map(|x| self.expr(x)).collect();
                let l = self.b.list(&ids);
                self.b.expr(Expr::Tuple(l))
            }
            E::Block(stmts, tail) => self.block(stmts, tail.as_deref()),
            E::Closure(ps, body) => {
                let params: Vec<hir_lang::ParamId> = ps
                    .iter()
                    .map(|p| {
                        let b = self.binder(*p, BinderKind::Param);
                        let pat = self.b.bind(b);
                        self.b.param(Param::new(pat))
                    })
                    .collect();
                let body = self.expr(body);
                let params = self.b.list(&params);
                self.b.expr(Expr::Closure(Closure {
                    params,
                    effects: Effects::YIELD,
                    implicit: Some(CaptureMode::ByRef),
                    ..Closure::new(body)
                }))
            }
            E::Yield(kv) => {
                let (key, value) = match kv {
                    Some((k, v)) => {
                        let k = k.as_deref().map(|k| self.expr(k));
                        (k, Some(self.expr(v)))
                    }
                    None => (None, None),
                };
                self.b.expr(Expr::Yield { key, value })
            }
            E::YieldFrom(x) => {
                let x = self.expr(x);
                self.b.expr(Expr::YieldFrom(x))
            }
            E::LetPlace(n, base, ix, body) => {
                let p = self.path(*base, Ns::Value);
                let base = self.b.expr(Expr::Path(p));
                let index = self.expr(ix);
                let place = self.b.expr(Expr::Index { base, index });
                let binder = self.binder(*n, BinderKind::Place);
                let body = self.expr(body);
                self.b.expr(Expr::LetPlace {
                    binder,
                    place,
                    body,
                })
            }
        }
    }

    fn block(&mut self, stmts: &[S], tail: Option<&E>) -> ExprId {
        let mut ids: Vec<StmtId> = Vec::new();
        for s in stmts {
            match s {
                S::Let(n, t, init) => {
                    let ty = t.as_ref().map(|t| self.ty(t));
                    let init = init.as_ref().map(|e| self.expr(e));
                    let b = self.binder(*n, BinderKind::Local);
                    let pat = self.b.bind(b);
                    ids.push(self.b.stmt(Stmt::Let {
                        pat,
                        ty,
                        init,
                        else_: None,
                    }));
                }
                S::Expr(e) => {
                    let x = self.expr(e);
                    ids.push(self.b.expr_stmt(x));
                }
                S::Fn(f) => {
                    let i = self.func(f);
                    ids.push(self.b.stmt(Stmt::Item(i)));
                }
            }
        }
        let tail = tail.map(|t| self.expr(t));
        self.b.block(&ids, tail)
    }

    fn func(&mut self, f: &F) -> ItemId {
        let slot = self.items.len();
        self.items.push(None);
        let tps: Vec<GenericParam> = f
            .tps
            .iter()
            .map(|t| GenericParam::new(self.binder(*t, BinderKind::TypeParam)))
            .collect();
        let params: Vec<hir_lang::ParamId> =
            f.ps.iter()
                .map(|p| {
                    let b = self.binder(*p, BinderKind::Param);
                    let pat = self.b.bind(b);
                    self.b.param(Param::new(pat))
                })
                .collect();
        let body = self.block(&f.body, f.tail.as_ref());
        self.span();
        let params = self.b.list(&params);
        let tps = self.b.list(&tps);
        let item = self.b.item(
            Item::new(
                Some(self.names[f.name as usize]),
                ItemKind::Fn(FnDef {
                    generics: Generics {
                        params: tps,
                        preds: hir_lang::List::EMPTY,
                    },
                    params,
                    effects: Effects::YIELD,
                    body: Some(body),
                    ..FnDef::default()
                }),
            )
            .with_name_span(Span::new(self.pos, self.pos + 1)),
        );
        self.items[slot] = Some(item);
        item
    }
}

fn build(prog: &Prog, names: &mut Interner) -> (Hir, Build) {
    let n = NAMES.map(|s| Name::new(names.intern(s)));
    let mut bd = Build {
        b: Builder::new(),
        names: n,
        binders: Vec::new(),
        items: Vec::new(),
        uses: Vec::new(),
        pos: 0,
    };
    let items: Vec<ItemId> = prog.items.iter().map(|it| bd.func(it)).collect();
    let root = bd.b.module(None, &items);
    let b = core::mem::replace(&mut bd.b, Builder::new());
    (b.finish(root).expect("valid"), bd)
}

/// Which paths the canonical walk reaches. Normalization turns a union's
/// dropped repeats into dead error paths, which nothing resolves.
fn live_paths(hir: &Hir) -> Vec<bool> {
    let mut live = vec![false; hir.count(hir_lang::IdKind::Path)];
    hir_lang::walk(hir, |n| {
        if let NodeRef::Path(p) = n {
            live[p.index()] = true;
        }
    });
    live
}

fn expected_res(e: Expect, bd: &Build) -> Res {
    match e {
        Expect::Local(i) => Res::Local(bd.binders[i]),
        Expect::Item(i) => Res::Def(DefId::foreign(
            UnitId::new(0),
            Def::Item(bd.items[i].unwrap()),
        )),
        Expect::Err => Res::Err,
    }
}

fn check_against_reference(prog: &Prog, after_decl: bool) -> Result<(), TestCaseError> {
    let mut names = Interner::new();
    let (hir, bd) = build(prog, &mut names);
    let live = live_paths(&hir);
    let expected = Reference::run(prog, after_decl);
    prop_assert_eq!(expected.len(), bd.uses.len());
    let policy = if after_decl {
        Policy::new().with_hoisting(ItemClass::Fn, Hoist::AfterDecl)
    } else {
        Policy::new()
    };
    let r = Resolver::new(policy).resolve(hir, &names).unwrap();
    let out = r.hir(UnitId::new(0)).unwrap();
    let mut live_uses = Vec::with_capacity(bd.uses.len());
    for (i, (&p, &e)) in bd.uses.iter().zip(&expected).enumerate() {
        let path = out.path(p);
        if live[p.index()] {
            prop_assert_eq!(path.res, expected_res(e, &bd), "use #{} of {:?}", i, prog);
            live_uses.push(p);
        } else {
            // A repeat normalization dropped: a dead error path, untouched.
            prop_assert_eq!((path.res, path.segments.len()), (Res::Err, 0));
            prop_assert!(
                r.diagnostics()
                    .iter()
                    .all(|d| d.node != Some(NodeRef::Path(p)))
            );
        }
    }
    check_one_diag_per_error(&r, &live_uses)?;
    check_index(&r)?;
    prop_assert!(out.validate().is_ok());
    Ok(())
}

/// Every reference resolves, or has exactly one diagnostic attached.
fn check_one_diag_per_error(r: &Resolution, uses: &[PathId]) -> Result<(), TestCaseError> {
    let hir = r.hir(UnitId::new(0)).unwrap();
    for &p in uses {
        let n = r
            .diagnostics()
            .iter()
            .filter(|d| d.node == Some(NodeRef::Path(p)))
            .count();
        let expect = usize::from(hir.path(p).res == Res::Err);
        prop_assert_eq!(n, expect);
    }
    Ok(())
}

/// Every reference's definition lists it, and only its own references.
fn check_index(r: &Resolution) -> Result<(), TestCaseError> {
    let ix = r.index();
    let mut total = 0;
    for (d, _) in ix.definitions().iter().enumerate() {
        let d = resolve_lang::DefRef::from_index(d);
        for reference in ix.references(d) {
            prop_assert_eq!(reference.def, d);
            total += 1;
        }
    }
    prop_assert_eq!(total, ix.references_all().len());
    for reference in ix.references_all() {
        prop_assert!(ix.references(reference.def).any(|r| r == reference));
        let unit = reference.location.unit;
        prop_assert_eq!(
            ix.resolve_at(unit, reference.path, reference.segment),
            Some(reference.def)
        );
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn prop_matches_reference_with_scope_hoisting(p in prog()) {
        check_against_reference(&p, false)?;
    }

    #[test]
    fn prop_matches_reference_with_declare_before_use(p in prog()) {
        check_against_reference(&p, true)?;
    }

    #[test]
    fn prop_resolution_is_deterministic(p in prog()) {
        let mut names = Interner::new();
        let (hir, _) = build(&p, &mut names);
        let a = resolve_lang::resolve(hir.clone(), &names).unwrap();
        let b = resolve_lang::resolve(hir, &names).unwrap();
        prop_assert_eq!(a.diagnostics(), b.diagnostics());
        prop_assert_eq!(a.hir(UnitId::new(0)), b.hir(UnitId::new(0)));
        prop_assert_eq!(a.index().references_all(), b.index().references_all());
    }

    /// With scope hoisting, the order of module items does not change what
    /// any name means.
    #[test]
    fn prop_hoisting_makes_item_order_irrelevant(p in prog(), seed in any::<u64>()) {
        // Distinct top-level names: with duplicates the first one wins, which
        // is order-dependent by definition.
        let mut p = p;
        let mut seen = [false; 5];
        p.items.retain(|it| !core::mem::replace(&mut seen[it.name as usize], true));
        let mut q = p.clone();
        let n = q.items.len();
        if n > 1 {
            let k = (seed as usize) % n;
            q.items.rotate_left(k);
        }
        // Compare what each use resolves to by *name of the item*, or
        // "a binder", via the HIR: ids are renumbered by the rotation.
        let mut names = Interner::new();
        let (hp, bp) = build(&p, &mut names);
        let (hq, bq) = build(&q, &mut names);
        let rp = resolve_lang::resolve(hp, &names).unwrap();
        let rq = resolve_lang::resolve(hq, &names).unwrap();
        let describe = |r: &Resolution, uses: &[PathId]| -> Vec<Option<(u8, u32)>> {
            let hir = r.hir(UnitId::new(0)).unwrap();
            uses.iter().map(|p| match hir.path(*p).res {
                Res::Def(d) => {
                    let Def::Item(i) = d.def() else { return None };
                    let name = hir.item(i).name.unwrap();
                    let span = hir.item(i).name_span;
                    Some((NAMES.iter().position(|s| names.get(s) == Some(name.sym)).unwrap() as u8, span.len()))
                }
                Res::Local(_) => Some((255, 0)),
                _ => None,
            }).collect()
        };
        // Uses inside rotated items move together; compare per item.
        let per_item = |prog: &Prog, desc: Vec<Option<(u8, u32)>>| {
            let mut out: Vec<(u8, Vec<Option<(u8, u32)>>)> = Vec::new();
            let mut it = desc.into_iter();
            for item in &prog.items {
                let count = count_uses(&item.body, item.tail.as_ref());
                out.push((item.name, it.by_ref().take(count).collect()));
            }
            out.sort_by_key(|x| x.0);
            out
        };
        let dp = per_item(&p, describe(&rp, &bp.uses));
        let dq = per_item(&q, describe(&rq, &bq.uses));
        prop_assert_eq!(dp, dq);
    }
}

fn count_uses(stmts: &[S], tail: Option<&E>) -> usize {
    fn t(x: &T) -> usize {
        match x {
            T::Name(_) | T::Nullable(_) => 1,
            T::Union(ts) | T::Inter(ts) => ts.iter().map(t).sum(),
        }
    }
    fn e(x: &E) -> usize {
        match x {
            E::Use(_) => 1,
            E::Tuple(xs) => xs.iter().map(e).sum(),
            E::Block(s, t) => count_uses(s, t.as_deref()),
            E::Closure(_, b) | E::YieldFrom(b) => e(b),
            E::Yield(None) => 0,
            E::Yield(Some((k, v))) => k.as_deref().map_or(0, e) + e(v),
            E::LetPlace(_, _, ix, body) => 1 + e(ix) + e(body),
        }
    }
    stmts
        .iter()
        .map(|s| match s {
            S::Let(_, ty, init) => ty.as_ref().map_or(0, t) + init.as_ref().map_or(0, e),
            S::Expr(x) => e(x),
            S::Fn(f) => count_uses(&f.body, f.tail.as_ref()),
        })
        .sum::<usize>()
        + tail.map_or(0, e)
}

/// The shrunk programs of the two failures this suite found in 0.2.0
/// (`properties.proptest-regressions`), restated in the 0.4 model: the
/// seeds there no longer generate them since the model gained forms.
#[test]
fn test_recorded_regressions_still_match_reference() {
    let f = |name, body: Vec<S>| F {
        name,
        tps: Vec::new(),
        ps: Vec::new(),
        body,
        tail: None,
    };
    let block = |s: Vec<S>| E::Block(s, None);
    // [(0, [], [Expr(Block([Expr(Block([Fn(2, [], [Let(0, Some(Use(1)))], None)], None)),
    //   Fn(1, [], [], None)], None))], None)]
    let first = Prog {
        items: vec![f(
            0,
            vec![S::Expr(block(vec![
                S::Expr(block(vec![S::Fn(f(
                    2,
                    vec![S::Let(0, None, Some(E::Use(1)))],
                ))])),
                S::Fn(f(1, Vec::new())),
            ]))],
        )],
    };
    // [(0, [], [Expr(Block([Expr(Block([Fn(0, [], [], None)], None)),
    //   Fn(3, [], [Let(0, Some(Use(3)))], None)], None))], None)]
    let second = Prog {
        items: vec![f(
            0,
            vec![S::Expr(block(vec![
                S::Expr(block(vec![S::Fn(f(0, Vec::new()))])),
                S::Fn(f(3, vec![S::Let(0, None, Some(E::Use(3)))])),
            ]))],
        )],
    };
    for p in [&first, &second] {
        for after_decl in [false, true] {
            check_against_reference(p, after_decl).unwrap();
        }
    }
}

/// Guards the generator: random programs must exercise locals, items,
/// captures across frames, unresolved names, and the 0.4 forms (place
/// aliases reached and blocked, generic parameters named from unions,
/// repeated union members that normalization drops), or
/// the differential tests above prove little.
#[test]
fn test_generator_covers_every_outcome() {
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;
    let mut runner = TestRunner::deterministic();
    let (mut local, mut item, mut err) = (0, 0, 0);
    let (mut place, mut type_param) = (0, 0);
    let (mut unions, mut yields, mut let_places, mut dropped) = (0, 0, 0, 0);
    for _ in 0..300 {
        let p = prog().new_tree(&mut runner).unwrap().current();
        let dbg = format!("{p:?}");
        unions += dbg.matches("Union(").count() + dbg.matches("Inter(").count();
        yields += dbg.matches("Yield").count();
        let_places += dbg.matches("LetPlace(").count();
        let mut names = Interner::new();
        let (hir, bd) = build(&p, &mut names);
        let live = live_paths(&hir);
        dropped += bd.uses.iter().filter(|u| !live[u.index()]).count();
        let r = Reference::run_full(&p, false);
        for e in &r.uses {
            match *e {
                Expect::Local(i) => {
                    local += 1;
                    match r.kinds[i] {
                        Entry::Place => place += 1,
                        Entry::TypeParam => type_param += 1,
                        Entry::Local | Entry::Item => {}
                    }
                }
                Expect::Item(_) => item += 1,
                Expect::Err => err += 1,
            }
        }
    }
    assert!(local > 50 && item > 50 && err > 50, "{local} {item} {err}");
    assert!(place > 20 && type_param > 20, "{place} {type_param}");
    assert!(
        unions > 50 && yields > 50 && let_places > 50,
        "{unions} {yields} {let_places}"
    );
    // Union repeats that normalization drops (dead paths) do occur.
    assert!(dropped > 10, "{dropped}");
}
