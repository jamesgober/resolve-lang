//! The HIR 0.4 forms: `let_place` (scoping, hygiene of template binders,
//! frames, shadowing, the index), keyed `yield` and `yield from`, union and
//! intersection types (including what normalization does to them), and HIR
//! repaired by lenient validation.

#![allow(clippy::unwrap_used, clippy::expect_used)]

mod common;

use common::{Kit, item_res, kinds, messages, res};
use hir_lang::{
    BinderKind, Builder, Effects, Expansion, ExpnId, ExpnKind, Expr, ExprId, FnDef, Hir, Name, Ns,
    ParamId, Path, PathId, Prim, Res, Segment, Span, Ty, TyId, UnitId, Vis,
};
use intern_lang::Interner;
use resolve_lang::{DefKind, DiagKind, Policy, Resolver, Shadowing, SymbolKind, Target};

// ----------------------------------------------------------------- helpers

/// `let_place binder = place in body`.
fn let_place(k: &mut Kit, binder: hir_lang::BinderId, place: ExprId, body: ExprId) -> ExprId {
    k.b.expr(Expr::LetPlace {
        binder,
        place,
        body,
    })
}

/// `base[index]`.
fn index(k: &mut Kit, base: ExprId, index: ExprId) -> ExprId {
    k.b.expr(Expr::Index { base, index })
}

/// `target = value`.
fn assign(k: &mut Kit, target: ExprId, value: ExprId) -> ExprId {
    k.b.expr(Expr::Assign {
        target,
        op: None,
        value,
    })
}

/// A template expansion (a desugaring at `call_site`).
fn expansion(k: &mut Kit, name: &str, call_site: Span) -> ExpnId {
    let name = k.names.intern(name);
    k.b.expansion(Expansion {
        kind: ExpnKind::Desugar,
        name,
        call_site,
        parent: ExpnId::ROOT,
        def_site: ExpnId::ROOT,
    })
}

/// A one-segment value path spelling `name` (with its mark) as an expression.
fn use_name(k: &mut Kit, name: Name) -> (ExprId, PathId) {
    k.tick(1);
    let seg = Segment::new(name, k.b.origin());
    let segs = k.b.list(&[seg]);
    let p = k.b.path(Path::new(segs, Ns::Value));
    (k.b.expr(Expr::Path(p)), p)
}

/// A generator function: `fn name(params) yield { body }`.
fn generator(k: &mut Kit, name: &str, params: &[ParamId], body: ExprId) -> hir_lang::ItemId {
    let params = k.b.list(params);
    k.item(
        name,
        hir_lang::ItemKind::Fn(FnDef {
            params,
            effects: Effects::YIELD,
            body: Some(body),
            ..FnDef::default()
        }),
        Vis::Private,
    )
}

/// `fn name(x: ty) {}`.
fn fn_with_param_ty(k: &mut Kit, name: &str, ty: TyId) -> hir_lang::ItemId {
    let b = k.binder("x", BinderKind::Param);
    let pat = k.b.bind(b);
    let param = k.b.param(hir_lang::Param {
        ty: Some(ty),
        ..hir_lang::Param::new(pat)
    });
    let body = k.block(&[], None);
    k.func(name, &[param], body)
}

fn union(k: &mut Kit, members: &[TyId]) -> TyId {
    let l = k.b.list(members);
    k.b.ty(Ty::Union(l))
}

fn intersection(k: &mut Kit, members: &[TyId]) -> TyId {
    let l = k.b.list(members);
    k.b.ty(Ty::Intersection(l))
}

/// Every path the canonical walk reaches (normalization can orphan some).
fn live_paths(hir: &Hir) -> Vec<PathId> {
    let mut out = Vec::new();
    hir_lang::walk(hir, |n| {
        if let hir_lang::NodeRef::Path(p) = n {
            out.push(p);
        }
    });
    out
}

/// A path hir-lang turned into a dead error path (normalization dropped it,
/// or a lenient repair cut it off): the resolver neither touched nor
/// diagnosed nor indexed it.
fn assert_dead(r: &resolve_lang::Resolution, p: PathId) {
    let hir = r.hir(UnitId::new(0)).unwrap();
    let path = hir.path(p);
    assert_eq!((path.res, path.segments.len()), (Res::Err, 0));
    assert!(
        r.diagnostics()
            .iter()
            .all(|d| d.node != Some(hir_lang::NodeRef::Path(p)))
    );
    assert_eq!(r.index().resolve_at(UnitId::new(0), p, 0), None);
}

// --------------------------------------------------------------- let_place

#[test]
fn test_let_place_binder_resolves_in_body_only() {
    // fn f(a, k) { let_place p = a[k] in p = p; p }
    let mut k = Kit::new();
    let (pa, a) = k.param("a");
    let (pk, kk) = k.param("k");
    let (base, p_a) = k.use_(&["a"]);
    let (ix_e, p_k) = k.use_(&["k"]);
    let place = index(&mut k, base, ix_e);
    let p = k.binder("p", BinderKind::Place);
    let (lhs, p_lhs) = k.use_(&["p"]);
    let (rhs, p_rhs) = k.use_(&["p"]);
    let body = assign(&mut k, lhs, rhs);
    let lp = let_place(&mut k, p, place, body);
    let s = k.stmt(lp);
    let (after, p_after) = k.use_(&["p"]);
    let fbody = k.block(&[s], Some(after));
    let f = k.func("f", &[pa, pk], fbody);
    let hir = k.finish(&[f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p_a).0, Res::Local(a));
    assert_eq!(res(&r, 0, p_k).0, Res::Local(kk));
    assert_eq!(res(&r, 0, p_lhs).0, Res::Local(p));
    assert_eq!(res(&r, 0, p_rhs).0, Res::Local(p));
    // Past the body the alias is gone.
    assert_eq!(res(&r, 0, p_after).0, Res::Err);
    assert!(matches!(
        kinds(&r)[..],
        [DiagKind::Unresolved { ns: Ns::Value, .. }]
    ));
    assert!(r.hir(UnitId::new(0)).unwrap().validate().is_ok());
}

#[test]
fn test_let_place_place_operands_see_outer_binder_of_same_name() {
    // fn f(p) { let_place p = p[0] in p }  -- the place's `p` is the parameter
    let mut k = Kit::new();
    let (pp, param) = k.param("p");
    let (base, p_base) = k.use_(&["p"]);
    let zero = k.b.int(0);
    let place = index(&mut k, base, zero);
    let alias = k.binder("p", BinderKind::Place);
    let (body, p_body) = k.use_(&["p"]);
    let lp = let_place(&mut k, alias, place, body);
    let fbody = k.block(&[], Some(lp));
    let f = k.func("f", &[pp], fbody);
    let hir = k.finish(&[f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p_base).0, Res::Local(param));
    assert_eq!(res(&r, 0, p_body).0, Res::Local(alias));
}

#[test]
fn test_let_place_nested_aliases_innermost_wins() {
    // fn f(a) { let_place p = a[0] in let_place p = p[1] in p }
    let mut k = Kit::new();
    let (pa, _) = k.param("a");
    let (base, _) = k.use_(&["a"]);
    let zero = k.b.int(0);
    let outer_place = index(&mut k, base, zero);
    let outer = k.binder("p", BinderKind::Place);
    let (inner_base, p_inner_base) = k.use_(&["p"]);
    let one = k.b.int(1);
    let inner_place = index(&mut k, inner_base, one);
    let inner = k.binder("p", BinderKind::Place);
    let (body, p_body) = k.use_(&["p"]);
    let inner_lp = let_place(&mut k, inner, inner_place, body);
    let outer_lp = let_place(&mut k, outer, outer_place, inner_lp);
    let fbody = k.block(&[], Some(outer_lp));
    let f = k.func("f", &[pa], fbody);
    let hir = k.finish(&[f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p_inner_base).0, Res::Local(outer));
    assert_eq!(res(&r, 0, p_body).0, Res::Local(inner));
}

/// Builds `fn tagger(items) { [let p = 1;] <template: let_place p'e = items[0] in p'e =
/// <user: p>> }` and returns the kit, the HIR, the user's local (if any),
/// the alias, the template's path, and the user's path.
fn template_case(
    with_user_local: bool,
) -> (
    Kit,
    Hir,
    Option<hir_lang::BinderId>,
    hir_lang::BinderId,
    PathId,
    PathId,
) {
    let mut k = Kit::new();
    // A parameter name far from `p`, so no legitimate suggestion exists.
    let (pa, _) = k.param("items");
    let mut stmts = Vec::new();
    let mut user = None;
    if with_user_local {
        let one = k.b.int(1);
        let (s, b) = k.let_("p", Some(one));
        stmts.push(s);
        user = Some(b);
    }
    let call_site = k.tick(10);
    let e = expansion(&mut k, "compound_assign", call_site);
    k.b.set_expansion(e);
    let (base, _) = k.use_(&["items"]);
    let zero = k.b.int(0);
    let place = index(&mut k, base, zero);
    let p_sym = k.names.intern("p");
    let alias = k.b.new_binder(Name::marked(p_sym, e), BinderKind::Place);
    let (lhs, p_template) = use_name(&mut k, Name::marked(p_sym, e));
    // The hole is user text: root mark.
    k.b.set_expansion(ExpnId::ROOT);
    let (rhs, p_user) = k.use_(&["p"]);
    k.b.set_expansion(e);
    let body = assign(&mut k, lhs, rhs);
    let lp = let_place(&mut k, alias, place, body);
    k.b.set_expansion(ExpnId::ROOT);
    stmts.push(k.stmt(lp));
    let fbody = k.block(&stmts, None);
    let f = k.func("tagger", &[pa], fbody);
    let hir = k.finish(&[f]);
    (k, hir, user, alias, p_template, p_user)
}

#[test]
fn test_let_place_template_binder_is_hygienic() {
    let (k, hir, user, alias, p_template, p_user) = template_case(true);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    // The template's marked `p` names its alias; the user's `p`, inside the
    // alias's body, still names the user's local.
    assert_eq!(res(&r, 0, p_template).0, Res::Local(alias));
    assert_eq!(res(&r, 0, p_user).0, Res::Local(user.unwrap()));
}

#[test]
fn test_let_place_template_binder_is_never_suggested_to_user_names() {
    // No user `p`: the user's `p` is unresolved, and the marked alias (the
    // same spelling) is not offered as "did you mean".
    let (k, hir, _, alias, p_template, p_user) = template_case(false);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p_template).0, Res::Local(alias));
    assert_eq!(res(&r, 0, p_user).0, Res::Err);
    assert_eq!(
        kinds(&r),
        [DiagKind::Unresolved {
            name: Name::new(k.names.get("p").unwrap()),
            ns: Ns::Value,
            container: None,
            suggestion: None,
        }]
    );
}

#[test]
fn test_let_place_template_alias_is_outside_source_for_rename() {
    let (k, hir, _, alias, _, _) = template_case(true);
    let unit = hir.unit();
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    let ix = r.index();
    let d = ix.def_of(Target::Local(unit, alias)).unwrap();
    let def = ix.definition(d).unwrap();
    assert_eq!(def.kind, SymbolKind::Place);
    assert_eq!(def.kind.name(), "place alias");
    assert_eq!(ix.references(d).len(), 1);
    // Everything about the alias came out of the template: a rename cannot
    // edit any of it. Its definition and its reference both map to the
    // expansion's call site, one location.
    let set = ix.rename_set(d);
    assert!(set.edits.is_empty(), "{:?}", set.edits);
    assert_eq!(set.outside_source.len(), 1);
    assert!(!set.outside_source[0].in_source);
    assert_eq!(set.outside_source, [def.location.unwrap()]);
    // Place aliases are not outline symbols.
    assert!(
        ix.document_symbols(unit)
            .iter()
            .all(|(_, d)| d.kind != SymbolKind::Place)
    );
}

#[test]
fn test_let_place_source_alias_is_renameable() {
    // fn f(a) { let_place p = a[0] in (p, p) }  with no expansion
    let mut k = Kit::new();
    let (pa, _) = k.param("a");
    let (base, _) = k.use_(&["a"]);
    let zero = k.b.int(0);
    let place = index(&mut k, base, zero);
    let alias = k.binder("p", BinderKind::Place);
    let (x, _) = k.use_(&["p"]);
    let (y, _) = k.use_(&["p"]);
    let body = k.tuple(&[x, y]);
    let lp = let_place(&mut k, alias, place, body);
    let fbody = k.block(&[], Some(lp));
    let f = k.func("f", &[pa], fbody);
    let hir = k.finish(&[f]);
    let unit = hir.unit();
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    let ix = r.index();
    let d = ix.def_of(Target::Local(unit, alias)).unwrap();
    assert_eq!(ix.references(d).len(), 2);
    let set = ix.rename_set(d);
    assert_eq!(set.edits.len(), 3, "{:?}", set.edits);
    assert!(set.outside_source.is_empty());
}

#[test]
fn test_let_place_alias_cannot_be_captured_by_closure() {
    // fn f(a) { let_place p = a[0] in (|| p) }  -- implicit captures, but a
    // place alias crosses no frame.
    let mut k = Kit::new();
    let (pa, a) = k.param("a");
    let (base, _) = k.use_(&["a"]);
    let zero = k.b.int(0);
    let place = index(&mut k, base, zero);
    let alias = k.binder("p", BinderKind::Place);
    let (inner, p_inner) = k.use_(&["p"]);
    let (also, p_a) = k.use_(&["a"]);
    let both = k.tuple(&[inner, also]);
    let c = k.closure(&[], both);
    let lp = let_place(&mut k, alias, place, c);
    let fbody = k.block(&[], Some(lp));
    let f = k.func("f", &[pa], fbody);
    let hir = k.finish(&[f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p_inner).0, Res::Err);
    // An ordinary parameter is still captured implicitly.
    assert_eq!(res(&r, 0, p_a).0, Res::Local(a));
    assert_eq!(
        kinds(&r),
        [DiagKind::CannotCapture {
            name: k.name("p"),
            binder: alias,
        }]
    );
    assert!(r.hir(UnitId::new(0)).unwrap().validate().is_ok());
}

#[test]
fn test_let_place_alias_is_exempt_from_shadowing_rules() {
    // fn f(a) { let p = 1; let_place p = a[0] in { let p = 2; p } }
    // Under both deny policies: the alias shadows nothing, and the inner
    // `let p` does not shadow the alias. (It does shadow the outer `let p`
    // under DenyLocals, which is the one diagnostic there.)
    for (shadowing, expect) in [(Shadowing::DenySameScope, 0), (Shadowing::DenyLocals, 1)] {
        let mut k = Kit::new();
        let (pa, _) = k.param("a");
        let one = k.b.int(1);
        let (s1, outer) = k.let_("p", Some(one));
        let (base, _) = k.use_(&["a"]);
        let zero = k.b.int(0);
        let place = index(&mut k, base, zero);
        let alias = k.binder("p", BinderKind::Place);
        let two = k.b.int(2);
        let (s2, inner) = k.let_("p", Some(two));
        let (tail, p_tail) = k.use_(&["p"]);
        let body = k.block(&[s2], Some(tail));
        let lp = let_place(&mut k, alias, place, body);
        let s3 = k.stmt(lp);
        let fbody = k.block(&[s1, s3], None);
        let f = k.func("f", &[pa], fbody);
        let hir = k.finish(&[f]);
        let r = Resolver::new(Policy::new().with_shadowing(shadowing))
            .resolve(hir, &k.names)
            .unwrap();
        assert_eq!(res(&r, 0, p_tail).0, Res::Local(inner));
        let shadows: Vec<_> = kinds(&r)
            .into_iter()
            .filter(|d| matches!(d, DiagKind::Shadowing { .. }))
            .collect();
        assert_eq!(shadows.len(), expect, "{shadowing:?}: {shadows:?}");
        for d in shadows {
            assert_eq!(
                d,
                DiagKind::Shadowing {
                    name: k.name("p"),
                    shadowed: outer,
                }
            );
        }
        let _ = alias;
    }
}

#[test]
fn test_let_place_body_item_competes_with_alias_by_scope() {
    // fn f(a) { let_place p = a[0] in { fn p() {} p } }  -- the block's item
    // is deeper than the alias, so it wins.
    let mut k = Kit::new();
    let (pa, _) = k.param("a");
    let (base, _) = k.use_(&["a"]);
    let zero = k.b.int(0);
    let place = index(&mut k, base, zero);
    let alias = k.binder("p", BinderKind::Place);
    let ib = k.block(&[], None);
    let item = k.func("p", &[], ib);
    let si = k.item_stmt(item);
    let (tail, p_tail) = k.use_(&["p"]);
    let body = k.block(&[si], Some(tail));
    let lp = let_place(&mut k, alias, place, body);
    let fbody = k.block(&[], Some(lp));
    let f = k.func("f", &[pa], fbody);
    let hir = k.finish(&[f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p_tail).0, item_res(0, item));
}

// ------------------------------------------------------------------- yield

#[test]
fn test_yield_key_value_and_yield_from_operands_resolve() {
    // fn g() {}
    // fn gen(k, v) yield { yield k => v; yield v; yield; yield from g; yield q => v }
    let mut k = Kit::new();
    let gb = k.block(&[], None);
    let g = k.func("g", &[], gb);
    let (pk, kb) = k.param("k");
    let (pv, vb) = k.param("v");
    let (key, p_key) = k.use_(&["k"]);
    let (val, p_val) = k.use_(&["v"]);
    let y1 = k.b.expr(Expr::Yield {
        key: Some(key),
        value: Some(val),
    });
    let (val2, p_val2) = k.use_(&["v"]);
    let y2 = k.b.expr(Expr::Yield {
        key: None,
        value: Some(val2),
    });
    let y3 = k.b.expr(Expr::Yield {
        key: None,
        value: None,
    });
    let (inner, p_inner) = k.use_(&["g"]);
    let y4 = k.b.expr(Expr::YieldFrom(inner));
    let (bad, p_bad) = k.use_(&["q"]);
    let (val3, p_val3) = k.use_(&["v"]);
    let y5 = k.b.expr(Expr::Yield {
        key: Some(bad),
        value: Some(val3),
    });
    let stmts: Vec<_> = [y1, y2, y3, y4, y5].iter().map(|e| k.stmt(*e)).collect();
    let body = k.block(&stmts, None);
    let gen_fn = generator(&mut k, "gen", &[pk, pv], body);
    let hir = k.finish(&[g, gen_fn]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p_key).0, Res::Local(kb));
    assert_eq!(res(&r, 0, p_val).0, Res::Local(vb));
    assert_eq!(res(&r, 0, p_val2).0, Res::Local(vb));
    assert_eq!(res(&r, 0, p_inner).0, item_res(0, g));
    assert_eq!(res(&r, 0, p_val3).0, Res::Local(vb));
    // The unknown key has exactly one diagnostic, at the key.
    assert_eq!(res(&r, 0, p_bad).0, Res::Err);
    let diags = r.diagnostics();
    assert_eq!(diags.len(), 1, "{:?}", messages(&r, &k.names));
    assert_eq!(diags[0].node, Some(hir_lang::NodeRef::Path(p_bad)));
}

// ------------------------------------------------------ unions/intersections

#[test]
fn test_union_and_intersection_members_resolve_like_type_paths() {
    // record Foo; record Bar; record Baz;
    // fn f<T>(x: (T | Foo | ?Bar) & Baz) {}
    let mut k = Kit::new();
    let foo = k.record("Foo", true, Vis::Private);
    let bar = k.record("Bar", true, Vis::Private);
    let baz = k.record("Baz", true, Vis::Private);
    let t = k.binder("T", BinderKind::TypeParam);
    let (t_ty, p_t) = k.ty(&["T"]);
    let (foo_ty, p_foo) = k.ty(&["Foo"]);
    let (bar_ty, p_bar) = k.ty(&["Bar"]);
    let nb = k.b.ty(Ty::Nullable(bar_ty));
    let u = union(&mut k, &[t_ty, foo_ty, nb]);
    let (baz_ty, p_baz) = k.ty(&["Baz"]);
    let i = intersection(&mut k, &[u, baz_ty]);
    let b = k.binder("x", BinderKind::Param);
    let pat = k.b.bind(b);
    let param = k.b.param(hir_lang::Param {
        ty: Some(i),
        ..hir_lang::Param::new(pat)
    });
    let body = k.block(&[], None);
    let gps = [hir_lang::GenericParam::new(t)];
    let gps = k.b.list(&gps);
    let params = k.b.list(&[param]);
    let f = k.item(
        "f",
        hir_lang::ItemKind::Fn(FnDef {
            generics: hir_lang::Generics {
                params: gps,
                preds: hir_lang::List::EMPTY,
            },
            params,
            body: Some(body),
            ..FnDef::default()
        }),
        Vis::Private,
    );
    let hir = k.finish(&[foo, bar, baz, f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p_t).0, Res::Local(t));
    assert_eq!(res(&r, 0, p_foo).0, item_res(0, foo));
    assert_eq!(res(&r, 0, p_bar).0, item_res(0, bar));
    assert_eq!(res(&r, 0, p_baz).0, item_res(0, baz));
}

#[test]
fn test_union_member_errors_are_one_diagnostic_each() {
    // fn g() {}  fn f(x: g | Nope) {}  -- a function is not a type; Nope is unknown.
    let mut k = Kit::new();
    let gb = k.block(&[], None);
    let g = k.func("g", &[], gb);
    let (g_ty, p_g) = k.ty(&["g"]);
    let (n_ty, p_n) = k.ty(&["Nope"]);
    let u = union(&mut k, &[g_ty, n_ty]);
    let f = fn_with_param_ty(&mut k, "f", u);
    let hir = k.finish(&[g, f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p_g).0, Res::Err);
    assert_eq!(res(&r, 0, p_n).0, Res::Err);
    let mut ks = kinds(&r);
    ks.sort_by_key(|d| matches!(d, DiagKind::Unresolved { .. }));
    assert_eq!(
        ks,
        [
            DiagKind::WrongKind {
                name: k.name("g"),
                ns: Ns::Type,
                found: DefKind::Fn,
            },
            DiagKind::Unresolved {
                name: k.name("Nope"),
                ns: Ns::Type,
                container: None,
                suggestion: None,
            },
        ]
    );
}

#[test]
fn test_union_repeated_member_is_dropped_before_resolution() {
    // record Foo;  fn f(x: Foo | Foo) {}  -- normalization keeps one `Foo`
    // (the union collapses to it); the dropped path is dead and never
    // resolved, diagnosed, or indexed.
    let mut k = Kit::new();
    let foo = k.record("Foo", true, Vis::Private);
    let (a, pa) = k.ty(&["Foo"]);
    let (b, pb) = k.ty(&["Foo"]);
    let u = union(&mut k, &[a, b]);
    let f = fn_with_param_ty(&mut k, "f", u);
    let hir = k.finish(&[foo, f]);
    let live = live_paths(&hir);
    assert_eq!(
        usize::from(live.contains(&pa)) + usize::from(live.contains(&pb)),
        1,
        "exactly one member survives normalization"
    );
    let (kept, dropped) = if live.contains(&pa) {
        (pa, pb)
    } else {
        (pb, pa)
    };
    let unit = hir.unit();
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, kept).0, item_res(0, foo));
    assert_dead(&r, dropped);
    let ix = r.index();
    let Res::Def(d) = item_res(0, foo) else {
        unreachable!()
    };
    let def = ix.def_of(Target::Def(d)).unwrap();
    assert_eq!(ix.references(def).len(), 1);
    assert_eq!(ix.resolve_at(unit, dropped, 0), None);
    assert!(r.hir(unit).unwrap().validate().is_ok());
}

#[test]
fn test_union_nested_and_nullable_members_resolve_after_flattening() {
    // record A; record B; record C;  fn f(x: ?A | (B | C)) {}
    // normalizes to ?(A | B | C); every path stays live and resolves.
    let mut k = Kit::new();
    let ra = k.record("A", true, Vis::Private);
    let rb = k.record("B", true, Vis::Private);
    let rc = k.record("C", true, Vis::Private);
    let (a, pa) = k.ty(&["A"]);
    let na = k.b.ty(Ty::Nullable(a));
    let (b, pb) = k.ty(&["B"]);
    let (c, pc) = k.ty(&["C"]);
    let inner = union(&mut k, &[b, c]);
    let u = union(&mut k, &[na, inner]);
    let f = fn_with_param_ty(&mut k, "f", u);
    let hir = k.finish(&[ra, rb, rc, f]);
    let live = live_paths(&hir);
    assert!([pa, pb, pc].iter().all(|p| live.contains(p)));
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, pa).0, item_res(0, ra));
    assert_eq!(res(&r, 0, pb).0, item_res(0, rb));
    assert_eq!(res(&r, 0, pc).0, item_res(0, rc));
}

// ------------------------------------------------------------ spec example

/// HIR.md §9.6, built the way lowering builds it (template names unresolved
/// and marked, the host function pre-resolved), resolved by this crate
/// under the PHP policy, and printed: the output is the spec's text.
#[test]
fn test_spec_9_6_mox_concat_assign_resolves_as_printed_in_the_spec() {
    let mut names = Interner::new();
    let mut b = Builder::new();
    let sym = |names: &mut Interner, s: &str| Name::new(names.intern(s));
    // function tag(string|int|null $k, array $a) { $a[$k] .= "!"; }
    let k_b = b.new_binder(sym(&mut names, "k"), BinderKind::Param);
    let k_pat = b.bind(k_b);
    let str_ty = b.ty(Ty::Prim(Prim::Str));
    let int_ty = b.ty(Ty::Prim(Prim::I64));
    let members = b.list(&[str_ty, int_ty]);
    let u = b.ty(Ty::Union(members));
    let k_ty = b.ty(Ty::Nullable(u));
    let k_param = b.param(hir_lang::Param {
        ty: Some(k_ty),
        ..hir_lang::Param::new(k_pat)
    });
    let a_b = b.new_binder(sym(&mut names, "a"), BinderKind::Param);
    let a_pat = b.bind(a_b);
    let a_param = b.param(hir_lang::Param::new(a_pat));
    let e1 = b.expansion(Expansion {
        kind: ExpnKind::Desugar,
        name: names.intern("compound_assign"),
        call_site: Span::new(60, 72),
        parent: ExpnId::ROOT,
        def_site: ExpnId::ROOT,
    });
    let a_use = b.name_expr(sym(&mut names, "a"));
    let k_use = b.name_expr(sym(&mut names, "k"));
    b.set_expansion(e1);
    let place = b.expr(Expr::Index {
        base: a_use,
        index: k_use,
    });
    let p_sym = names.intern("p");
    let p = b.new_binder(Name::marked(p_sym, e1), BinderKind::Place);
    let lhs = b.name_expr(Name::marked(p_sym, e1));
    let concat_sym = names.intern("concat");
    let host = names.intern("mox.concat");
    let concat_path = b.resolved_path(Name::new(concat_sym), Ns::Value, Res::Extern(host));
    let concat = b.expr(Expr::Path(concat_path));
    let read = b.name_expr(Name::marked(p_sym, e1));
    let bang = b.str_lit("!");
    let call = b.call(concat, &[read, bang]);
    let body = b.expr(Expr::Assign {
        target: lhs,
        op: None,
        value: call,
    });
    let lp = b.expr(Expr::LetPlace {
        binder: p,
        place,
        body,
    });
    b.set_expansion(ExpnId::ROOT);
    let s = b.expr_stmt(lp);
    let fbody = b.block(&[s], None);
    let tag = b.func(sym(&mut names, "tag"), &[k_param, a_param], fbody);
    let root = b.module(None, &[tag]);
    let hir = b.finish(root).unwrap();
    let r = Resolver::new(Policy::php()).resolve(hir, &names).unwrap();
    assert!(r.is_clean(), "{:?}", r.diagnostics());
    let printed = hir_lang::print(r.hir(UnitId::new(0)).unwrap(), &names);
    let spec = "\
(module
  (fn tag
    (param normal
      (bind k%0)
      (nullable
        (union
          (prim i64)
          (prim str))))
    (param normal
      (bind a%1))
    (block
      (do
        (let-place p%2'e1
          (index
            (use (path a → local a%1))
            (use (path k → local k%0)))
          (assign
            (use (path p'e1 → local p%2'e1))
            (call
              (use (path concat → extern mox.concat))
              (use (path p'e1 → local p%2'e1))
              (lit \"!\"))))))))";
    assert_eq!(printed, spec);
}

// ---------------------------------------------------------------- lenient

#[test]
fn test_lenient_repairs_leave_dead_subtrees_unresolved() {
    // fn f(a) { let_place p = g() in p; yield a; a }
    // The call is not a place, and `f` is no generator: lenient validation
    // turns both forms into errors and cuts their operands off. Resolution
    // leaves the dead paths alone and resolves the rest.
    let mut k = Kit::new();
    let (pa, a) = k.param("a");
    let (callee, p_g) = k.use_(&["g"]);
    let call = k.b.call(callee, &[]);
    let alias = k.binder("p", BinderKind::Place);
    let (body, p_body) = k.use_(&["p"]);
    let lp = let_place(&mut k, alias, call, body);
    let (ya, p_ya) = k.use_(&["a"]);
    let y = k.b.expr(Expr::Yield {
        key: None,
        value: Some(ya),
    });
    let (tail, p_tail) = k.use_(&["a"]);
    let s1 = k.stmt(lp);
    let s2 = k.stmt(y);
    let fbody = k.block(&[s1, s2], Some(tail));
    let f = k.func("f", &[pa], fbody);
    let root = k.root(&[f]);
    let builder = core::mem::replace(&mut k.b, Builder::new());
    let (hir, problems) = builder.finish_lenient(root).unwrap();
    assert_eq!(problems.len(), 2, "{problems:?}");
    let live = live_paths(&hir);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p_tail).0, Res::Local(a));
    for p in [p_g, p_body, p_ya] {
        assert!(!live.contains(&p), "repairs cut {p:?} off");
        assert_dead(&r, p);
    }
    assert!(r.hir(UnitId::new(0)).unwrap().validate().is_ok());
}

// ------------------------------------------- why not `lookup_local_in` (P13)

/// `fn f<T>() { (t::new, T) }`: builds the unit and returns the kit, the
/// HIR, the type parameter, and the two paths.
fn type_param_case() -> (Kit, Hir, hir_lang::BinderId, PathId, PathId) {
    let mut k = Kit::new();
    let t = k.binder("T", BinderKind::TypeParam);
    let (prefix, p_prefix) = k.use_(&["t", "new"]);
    let (bare, p_bare) = k.use_(&["T"]);
    let tuple = k.tuple(&[prefix, bare]);
    let body = k.block(&[], Some(tuple));
    let f = k.generic_fn("f", &[t], body);
    let hir = k.finish(&[f]);
    (k, hir, t, p_prefix, p_bare)
}

#[test]
fn test_type_param_prefix_is_found_through_a_case_folded_type_table() {
    // Under PHP the type table folds case, so the value path `t::new` finds
    // the type parameter `T` (an exact-name `lookup_local_in` would not).
    let (k, hir, t, p_prefix, _) = type_param_case();
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p_prefix), (Res::Local(t), 1));
}

#[test]
fn test_type_param_in_a_merged_table_is_the_wrong_kind_for_a_value() {
    // Under Python every namespace is one table, so the bare value path `T`
    // meets the type parameter there and is reported as the wrong kind,
    // where a separate value table would report it unresolved.
    let (mut k, hir, _, _, p_bare) = type_param_case();
    let r = Resolver::new(Policy::python())
        .resolve(hir, &k.names)
        .unwrap();
    assert_eq!(res(&r, 0, p_bare).0, Res::Err);
    assert!(
        kinds(&r).contains(&DiagKind::WrongKind {
            name: k.name("T"),
            ns: Ns::Value,
            found: DefKind::Local,
        }),
        "{:?}",
        messages(&r, &k.names)
    );
    let (k, hir, _, _, p_bare) = type_param_case();
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p_bare).0, Res::Err);
    assert!(
        kinds(&r)
            .iter()
            .any(|d| matches!(d, DiagKind::Unresolved { ns: Ns::Value, .. })),
        "{:?}",
        messages(&r, &k.names)
    );
}
