//! Property tests: resolve-lang against a simple reference resolver on
//! random scoped programs, plus the DIRECTIVES §4 invariants (one binder or
//! one diagnostic per reference, determinism and order independence under
//! hoisting, index consistency).

// Test models are small tuple-heavy trees; naming every tuple type would
// only add noise.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::type_complexity)]

use hir_lang::{
    Binder, BinderKind, Builder, CaptureMode, Closure, Def, DefId, Expr, ExprId, FnDef, Hir, Item,
    ItemId, ItemKind, Name, NodeRef, Ns, Param, Path, PathId, Res, Segment, Span, Stmt, StmtId,
    UnitId,
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
}

#[derive(Clone, Debug)]
enum S {
    Let(u8, Option<E>),
    Fn(u8, Vec<u8>, Vec<S>, Option<E>),
    Expr(E),
}

#[derive(Clone, Debug)]
struct Prog {
    items: Vec<(u8, Vec<u8>, Vec<S>, Option<E>)>,
}

const NAMES: [&str; 5] = ["a", "b", "c", "d", "e"];

fn expr() -> impl Strategy<Value = E> {
    let leaf = (0u8..5).prop_map(E::Use);
    leaf.prop_recursive(5, 48, 4, |inner| {
        let stmt = prop_oneof![
            ((0u8..5), proptest::option::of(inner.clone())).prop_map(|(n, e)| S::Let(n, e)),
            (
                (0u8..5),
                proptest::collection::vec(0u8..5, 0..2),
                proptest::collection::vec(
                    ((0u8..5), proptest::option::of(inner.clone())).prop_map(|(n, e)| S::Let(n, e)),
                    0..3
                ),
                proptest::option::of(inner.clone())
            )
                .prop_map(|(n, ps, body, tail)| S::Fn(n, ps, body, tail)),
            inner.clone().prop_map(S::Expr),
        ];
        prop_oneof![
            (
                proptest::collection::vec(stmt, 0..4),
                proptest::option::of(inner.clone())
            )
                .prop_map(|(s, t)| E::Block(s, t.map(Box::new))),
            (proptest::collection::vec(0u8..5, 0..2), inner.clone())
                .prop_map(|(ps, b)| E::Closure(ps, Box::new(b))),
            proptest::collection::vec(inner, 1..4).prop_map(E::Tuple),
        ]
    })
}

fn prog() -> impl Strategy<Value = Prog> {
    proptest::collection::vec(
        (
            0u8..5,
            proptest::collection::vec(0u8..5, 0..3),
            proptest::collection::vec(expr().prop_map(S::Expr), 0..3),
            proptest::option::of(expr()),
        ),
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

struct RScope {
    kind: Kind,
    /// (name, target, is_local, seq)
    entries: Vec<(u8, Expect, bool, u64)>,
}

/// The obvious, slow resolver: a stack of scopes searched innermost-out.
struct Reference {
    scopes: Vec<RScope>,
    seq: u64,
    binders: usize,
    items: usize,
    uses: Vec<Expect>,
    after_decl: bool,
}

impl Reference {
    fn tick(&mut self) -> u64 {
        self.seq += 1;
        self.seq
    }

    fn lookup(&self, n: u8) -> Expect {
        let mut crossed_fn = false;
        for scope in self.scopes.iter().rev() {
            let best = scope
                .entries
                .iter()
                .filter(|e| e.0 == n)
                .max_by_key(|e| e.3);
            if let Some(&(_, target, local, _)) = best {
                return if local && crossed_fn {
                    Expect::Err
                } else {
                    target
                };
            }
            if scope.kind == Kind::FnItem {
                crossed_fn = true;
            }
        }
        Expect::Err
    }

    fn push_item(&mut self, n: u8, idx: usize) {
        let seq = self.tick();
        let scope = self.scopes.last_mut().unwrap();
        // Duplicates: the first definition is kept.
        if !scope.entries.iter().any(|e| e.0 == n && !e.2) {
            scope.entries.push((n, Expect::Item(idx), false, seq));
        }
    }

    fn push_local(&mut self, n: u8) {
        let idx = self.binders;
        self.binders += 1;
        let seq = self.tick();
        self.scopes
            .last_mut()
            .unwrap()
            .entries
            .push((n, Expect::Local(idx), true, seq));
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
                    self.push_local(*p);
                }
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
                if let S::Fn(n, ..) = s {
                    self.push_item(*n, i);
                }
            }
        }
        for (s, &i) in stmts.iter().zip(&starts) {
            self.items = i;
            match s {
                S::Let(n, init) => {
                    if let Some(e) = init {
                        self.expr(e);
                    }
                    self.push_local(*n);
                }
                S::Expr(e) => self.expr(e),
                S::Fn(n, ps, body, tail) => {
                    if self.after_decl {
                        self.push_item(*n, i);
                    }
                    self.items = i + 1;
                    self.func(ps, body, tail.as_ref());
                }
            }
        }
        self.items = idx;
        if let Some(t) = tail {
            self.expr(t);
        }
        self.scopes.pop();
    }

    fn func(&mut self, ps: &[u8], body: &[S], tail: Option<&E>) {
        self.open(Kind::FnItem);
        for p in ps {
            self.push_local(*p);
        }
        self.block(body, tail);
        self.scopes.pop();
    }

    fn run(prog: &Prog, after_decl: bool) -> Vec<Expect> {
        let mut r = Reference {
            scopes: Vec::new(),
            seq: 0,
            binders: 0,
            items: 0,
            uses: Vec::new(),
            after_decl,
        };
        r.open(Kind::Module);
        let mut reserved = Vec::new();
        let mut idx = 0;
        for it in &prog.items {
            reserved.push(idx);
            idx += 1 + count_items(&it.2, it.3.as_ref());
        }
        if !after_decl {
            for (it, i) in prog.items.iter().zip(&reserved) {
                r.push_item(it.0, *i);
            }
        }
        for (it, i) in prog.items.iter().zip(&reserved) {
            if after_decl {
                r.push_item(it.0, *i);
            }
            r.items = i + 1;
            r.func(&it.1, &it.2, it.3.as_ref());
        }
        r.uses
    }
}

fn count_items_stmt(s: &S) -> usize {
    match s {
        S::Fn(_, _, body, tail) => 1 + count_items(body, tail.as_ref()),
        S::Let(_, Some(e)) | S::Expr(e) => count_items_expr(e),
        S::Let(_, None) => 0,
    }
}

fn count_items(stmts: &[S], tail: Option<&E>) -> usize {
    stmts.iter().map(count_items_stmt).sum::<usize>() + tail.map_or(0, count_items_expr)
}

fn count_items_expr(e: &E) -> usize {
    match e {
        E::Use(_) => 0,
        E::Tuple(xs) => xs.iter().map(count_items_expr).sum(),
        E::Block(s, t) => count_items(s, t.as_deref()),
        E::Closure(_, b) => count_items_expr(b),
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

    fn expr(&mut self, e: &E) -> ExprId {
        match e {
            E::Use(n) => {
                self.span();
                let seg = Segment::new(self.names[*n as usize], self.b.origin());
                let segs = self.b.list(&[seg]);
                let p = self.b.path(Path::new(segs, Ns::Value));
                self.uses.push(p);
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
                    implicit: Some(CaptureMode::ByRef),
                    ..Closure::new(body)
                }))
            }
        }
    }

    fn block(&mut self, stmts: &[S], tail: Option<&E>) -> ExprId {
        let mut ids: Vec<StmtId> = Vec::new();
        for s in stmts {
            match s {
                S::Let(n, init) => {
                    let init = init.as_ref().map(|e| self.expr(e));
                    let b = self.binder(*n, BinderKind::Local);
                    let pat = self.b.bind(b);
                    ids.push(self.b.let_stmt(pat, init));
                }
                S::Expr(e) => {
                    let x = self.expr(e);
                    ids.push(self.b.expr_stmt(x));
                }
                S::Fn(n, ps, body, tail) => {
                    let i = self.func(*n, ps, body, tail.as_ref());
                    ids.push(self.b.stmt(Stmt::Item(i)));
                }
            }
        }
        let tail = tail.map(|t| self.expr(t));
        self.b.block(&ids, tail)
    }

    fn func(&mut self, n: u8, ps: &[u8], body: &[S], tail: Option<&E>) -> ItemId {
        let slot = self.items.len();
        self.items.push(None);
        let params: Vec<hir_lang::ParamId> = ps
            .iter()
            .map(|p| {
                let b = self.binder(*p, BinderKind::Param);
                let pat = self.b.bind(b);
                self.b.param(Param::new(pat))
            })
            .collect();
        let body = self.block(body, tail);
        self.span();
        let params = self.b.list(&params);
        let item = self.b.item(
            Item::new(
                Some(self.names[n as usize]),
                ItemKind::Fn(FnDef {
                    params,
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
    let items: Vec<ItemId> = prog
        .items
        .iter()
        .map(|it| bd.func(it.0, &it.1, &it.2, it.3.as_ref()))
        .collect();
    let root = bd.b.module(None, &items);
    let b = core::mem::replace(&mut bd.b, Builder::new());
    (b.finish(root).expect("valid"), bd)
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
    let expected = Reference::run(prog, after_decl);
    prop_assert_eq!(expected.len(), bd.uses.len());
    let policy = if after_decl {
        Policy::new().with_hoisting(ItemClass::Fn, Hoist::AfterDecl)
    } else {
        Policy::new()
    };
    let r = Resolver::new(policy).resolve(hir, &names).unwrap();
    let out = r.hir(UnitId::new(0)).unwrap();
    for (i, (&p, &e)) in bd.uses.iter().zip(&expected).enumerate() {
        let got = out.path(p).res;
        prop_assert_eq!(got, expected_res(e, &bd), "use #{} of {:?}", i, prog);
    }
    check_one_diag_per_error(&r, &bd.uses)?;
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
        p.items.retain(|it| !core::mem::replace(&mut seen[it.0 as usize], true));
        let mut q = p.clone();
        let n = q.items.len();
        if n > 1 {
            let k = (seed as usize) % n;
            q.items.rotate_left(k);
        }
        let ep = Reference::run(&p, false);
        let eq = Reference::run(&q, false);
        // The reference itself agrees up to renumbering; compare what each
        // use resolves to by *name of the item or binder*, via the HIR.
        let mut names = Interner::new();
        let (hp, bp) = build(&p, &mut names);
        let (hq, bq) = build(&q, &mut names);
        let rp = resolve_lang::resolve(hp, &names).unwrap();
        let rq = resolve_lang::resolve(hq, &names).unwrap();
        let describe = |r: &Resolution, b: &Build, uses: &[PathId]| -> Vec<Option<(u8, u32)>> {
            let hir = r.hir(UnitId::new(0)).unwrap();
            uses.iter().map(|p| match hir.path(*p).res {
                Res::Def(d) => {
                    let Def::Item(i) = d.def() else { return None };
                    let name = hir.item(i).name.unwrap();
                    let span = hir.item(i).name_span;
                    let _ = b;
                    Some((NAMES.iter().position(|s| names.get(s) == Some(name.sym)).unwrap() as u8, span.len()))
                }
                Res::Local(_) => Some((255, 0)),
                _ => None,
            }).collect()
        };
        let _ = (ep, eq);
        // Uses inside rotated items move together; compare per item.
        let per_item = |prog: &Prog, desc: Vec<Option<(u8, u32)>>| {
            let mut out: Vec<(u8, Vec<Option<(u8, u32)>>)> = Vec::new();
            let mut it = desc.into_iter();
            for item in &prog.items {
                let count = count_uses(&item.2, item.3.as_ref());
                out.push((item.0, it.by_ref().take(count).collect()));
            }
            out.sort_by_key(|x| x.0);
            out
        };
        let dp = per_item(&p, describe(&rp, &bp, &bp.uses));
        let dq = per_item(&q, describe(&rq, &bq, &bq.uses));
        prop_assert_eq!(dp, dq);
    }
}

fn count_uses(stmts: &[S], tail: Option<&E>) -> usize {
    fn e(x: &E) -> usize {
        match x {
            E::Use(_) => 1,
            E::Tuple(xs) => xs.iter().map(e).sum(),
            E::Block(s, t) => count_uses(s, t.as_deref()),
            E::Closure(_, b) => e(b),
        }
    }
    stmts
        .iter()
        .map(|s| match s {
            S::Let(_, Some(x)) | S::Expr(x) => e(x),
            S::Let(_, None) => 0,
            S::Fn(_, _, body, t) => count_uses(body, t.as_ref()),
        })
        .sum::<usize>()
        + tail.map_or(0, e)
}

/// Guards the generator: random programs must exercise locals, items,
/// captures across frames, and unresolved names, or the differential tests
/// above prove little.
#[test]
fn test_generator_covers_every_outcome() {
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;
    let mut runner = TestRunner::deterministic();
    let (mut local, mut item, mut err) = (0, 0, 0);
    for _ in 0..300 {
        let p = prog().new_tree(&mut runner).unwrap().current();
        for e in Reference::run(&p, false) {
            match e {
                Expect::Local(_) => local += 1,
                Expect::Item(_) => item += 1,
                Expect::Err => err += 1,
            }
        }
    }
    assert!(local > 50 && item > 50 && err > 50, "{local} {item} {err}");
}
