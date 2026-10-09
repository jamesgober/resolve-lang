//! Hostile shapes: very deep nesting and very wide scopes never overflow the
//! stack and stay fast.

#![allow(clippy::unwrap_used, clippy::expect_used)]

mod common;

use common::{Kit, item_res, res};
use hir_lang::{BinderKind, Ns, PathRoot, Res, Vis};
use resolve_lang::{Policy, Resolver};

const DEPTH: usize = 100_000;

#[test]
fn test_deeply_nested_blocks() {
    // { let v0 = 1; { let v1 = v0; { ... { v0 } } } }  with an item per level
    let mut k = Kit::new();
    let one = k.b.int(1);
    let (outer_let, v0) = k.let_("v0", Some(one));
    let (mut inner, p) = k.use_(&["v0"]);
    let mut paths = Vec::new();
    for i in (1..DEPTH).rev() {
        let (u, pu) = k.use_(&["v0"]);
        paths.push(pu);
        let (s, _) = k.let_(&format!("v{}", i % 7 + 1), Some(u));
        let ib = k.block(&[], None);
        let f = k.func("helper", &[], ib);
        let si = k.item_stmt(f);
        inner = k.block(&[s, si], Some(inner));
    }
    let body = k.block(&[outer_let], Some(inner));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean());
    assert_eq!(res(&r, 0, p).0, Res::Local(v0));
    for p in paths.iter().step_by(997) {
        assert_eq!(res(&r, 0, *p).0, Res::Local(v0));
    }
}

#[test]
fn test_deeply_nested_closures_capture_outermost() {
    let mut k = Kit::new();
    let one = k.b.int(1);
    let (s, x) = k.let_("x", Some(one));
    let (mut e, p) = k.use_(&["x"]);
    for _ in 0..DEPTH / 4 {
        e = k.closure(&[], e);
    }
    let body = k.block(&[s], Some(e));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean());
    assert_eq!(res(&r, 0, p).0, Res::Local(x));
}

#[test]
fn test_deeply_nested_modules_with_super() {
    // mod m0 { fn f() {} mod m1 { mod m2 { ... fn g() { super::super::...::f } } } }
    let depth = 2_000;
    let mut k = Kit::new();
    let (e, p) = k.use_root(&["f"], PathRoot::Super(255));
    let gb = k.block(&[], Some(e));
    let g = k.func("g", &[], gb);
    let mut inner = k.module("deep", &[g], Vis::Private);
    for i in 0..depth {
        inner = k.module(&format!("m{i}"), &[inner], Vis::Private);
    }
    let fb = k.block(&[], None);
    let f = k.func("f", &[], fb);
    let top = k.module("top", &[f, inner], Vis::Private);
    let hir = k.finish(&[top]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    // 255 levels up from `deep` lands inside the chain, not at `top`.
    assert_eq!(res(&r, 0, p).0, Res::Err);
    assert_eq!(r.diagnostics().len(), 1);
}

#[test]
fn test_wide_module_and_many_references() {
    let n = 50_000;
    let mut k = Kit::new();
    let mut items = Vec::new();
    for i in 0..n {
        let b = k.block(&[], None);
        items.push(k.func_vis(&format!("f{i}"), &[], b, Vis::Public));
    }
    let mut uses = Vec::new();
    let mut paths = Vec::new();
    for i in 0..n {
        let (u, p) = k.use_(&[&format!("f{}", (i * 7919) % n)]);
        uses.push(u);
        paths.push((p, (i * 7919) % n));
    }
    let t = k.tuple(&uses);
    let body = k.block(&[], Some(t));
    items.push(k.func("main", &[], body));
    let first = items[0];
    let hir = k.finish(&items);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean());
    let (p, target) = paths[1];
    assert_eq!(res(&r, 0, p).0, item_res(0, items[target]));
    let d = r
        .index()
        .def_of(resolve_lang::Target::Def(match item_res(0, first) {
            Res::Def(d) => d,
            _ => unreachable!(),
        }))
        .unwrap();
    assert_eq!(r.index().references(d).len(), 1);
}

#[test]
fn test_many_type_parameters_deeply_nested() {
    // fn f<T0>() { fn g<T1>() { ... } }  each referencing its own T as `T::x`
    let depth = 5_000;
    let mut k = Kit::new();
    let mut paths = Vec::new();
    let mut inner: Option<hir_lang::ItemId> = None;
    for _ in 0..depth {
        let t = k.binder("T", BinderKind::TypeParam);
        let (e, p) = k.use_(&["T", "x"]);
        paths.push((p, t));
        let stmts: Vec<_> = inner.iter().map(|i| k.item_stmt(*i)).collect();
        let body = k.block(&stmts, Some(e));
        inner = Some(k.generic_fn("f", &[t], body));
    }
    let hir = k.finish(&[inner.unwrap()]);
    let r = Resolver::new(Policy::new()).resolve(hir, &k.names).unwrap();
    assert!(r.is_clean());
    for (p, t) in paths.iter().step_by(499) {
        assert_eq!(res(&r, 0, *p), (Res::Local(*t), 1));
    }
    let _ = Ns::Type;
}

#[test]
fn test_python_nested_class_bodies_skip_in_constant_time() {
    // x = 0;  class C: x = 1; def m(): class C: x = 1; def m(): ... return x
    let depth = 20_000;
    let mut k = Kit::new();
    let zero = k.b.int(0);
    let module_x = k.global("x", Some(zero), Vis::Public);
    let mut uses = Vec::new();
    let mut members = Vec::new();
    for _ in 0..50 {
        let (u, p) = k.use_(&["x"]);
        uses.push(u);
        members.push(p);
    }
    let t = k.tuple(&uses);
    let mb = k.block(&[], Some(t));
    let m = k.func_vis("m", &[], mb, Vis::Public);
    let one = k.b.int(1);
    let cx = k.global("x", Some(one), Vis::Public);
    let mut class = k.class("C", &[], &[cx, m], false);
    // Classes nest through method bodies (HIR class bodies hold no classes).
    for _ in 0..depth {
        let s = k.item_stmt(class);
        let mb = k.block(&[s], None);
        let m = k.func_vis("m", &[], mb, Vis::Public);
        let one = k.b.int(1);
        let cx = k.global("x", Some(one), Vis::Public);
        class = k.class("C", &[], &[cx, m], false);
    }
    let hir = k.finish(&[module_x, class]);
    let r = Resolver::new(Policy::python())
        .resolve(hir, &k.names)
        .unwrap();
    for p in members {
        assert_eq!(res(&r, 0, p).0, item_res(0, module_x));
    }
}
