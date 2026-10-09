//! Lexical resolution within one unit: binders, items, hoisting, shadowing
//! between them, frames, paths through modules and sums, patterns.

#![allow(clippy::unwrap_used, clippy::expect_used)]

mod common;

use common::{Kit, item_res, kinds, messages, res, variant_res};
use hir_lang::{BinderKind, Ns, PathRoot, Res, Vis};
use resolve_lang::{DefKind, DiagKind, Hoist, ItemClass, Policy, Resolver};

#[test]
fn test_local_and_param_resolve_to_binders() {
    let mut k = Kit::new();
    let (p, x) = k.param("x");
    let (one, _) = k.use_(&["x"]);
    let (s, y) = k.let_("y", Some(one));
    let (use_y, py) = k.use_(&["y"]);
    let (_, px) = {
        let e = k.b.expr(hir_lang::Expr::Err);
        (e, py)
    };
    let body = k.block(&[s], Some(use_y));
    let f = k.func("f", &[p], body);
    let hir = k.finish(&[f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, py).0, Res::Local(y));
    let _ = (x, px);
}

#[test]
fn test_items_are_hoisted_by_default_and_shadowed_by_later_lets() {
    // fn main() { let a = g; let g = 1; g }  fn g() {}
    let mut k = Kit::new();
    let (use_g1, p1) = k.use_(&["g"]);
    let (s1, _) = k.let_("a", Some(use_g1));
    let one = k.b.int(1);
    let (s2, g_local) = k.let_("g", Some(one));
    let (use_g2, p2) = k.use_(&["g"]);
    let body = k.block(&[s1, s2], Some(use_g2));
    let main = k.func("main", &[], body);
    let gb = k.block(&[], None);
    let g = k.func("g", &[], gb);
    let hir = k.finish(&[main, g]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p1).0, item_res(0, g));
    assert_eq!(res(&r, 0, p2).0, Res::Local(g_local));
}

#[test]
fn test_after_decl_hoisting_hides_later_items() {
    // fn main() { g }  fn g() {}   with declare-before-use functions
    let mut k = Kit::new();
    let (use_g, p) = k.use_(&["g"]);
    let body = k.block(&[], Some(use_g));
    let main = k.func("main", &[], body);
    let gb = k.block(&[], None);
    let g = k.func("g", &[], gb);
    // g recursing on itself is fine: visible from its own declaration on.
    let hir = k.finish(&[main, g]);
    let policy = Policy::new().with_hoisting(ItemClass::Fn, Hoist::AfterDecl);
    let r = Resolver::new(policy).resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p).0, Res::Err);
    assert!(matches!(kinds(&r)[..], [DiagKind::Unresolved { .. }]));
}

#[test]
fn test_after_decl_allows_recursion() {
    let mut k = Kit::new();
    let (use_f, p) = k.use_(&["f"]);
    let body = k.block(&[], Some(use_f));
    let f = k.func("f", &[], body);
    let hir = k.finish(&[f]);
    let policy = Policy::new().with_hoisting(ItemClass::Fn, Hoist::AfterDecl);
    let r = Resolver::new(policy).resolve(hir, &k.names).unwrap();
    assert!(r.is_clean());
    assert_eq!(res(&r, 0, p).0, item_res(0, f));
}

#[test]
fn test_block_item_shadows_outer_let() {
    // fn main() { let x = 1; { fn x() {} x } }
    let mut k = Kit::new();
    let one = k.b.int(1);
    let (s, _) = k.let_("x", Some(one));
    let xb = k.block(&[], None);
    let xf = k.func("x", &[], xb);
    let si = k.item_stmt(xf);
    let (use_x, p) = k.use_(&["x"]);
    let inner = k.block(&[si], Some(use_x));
    let body = k.block(&[s], Some(inner));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p).0, item_res(0, xf));
}

#[test]
fn test_nested_fn_cannot_capture_outer_local() {
    // fn main() { let x = 1; fn inner() { x } }
    let mut k = Kit::new();
    let one = k.b.int(1);
    let (s, x) = k.let_("x", Some(one));
    let (use_x, p) = k.use_(&["x"]);
    let ib = k.block(&[], Some(use_x));
    let inner = k.func("inner", &[], ib);
    let si = k.item_stmt(inner);
    let body = k.block(&[s, si], None);
    let main = k.func("main", &[], body);
    let hir = k.finish(&[main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p).0, Res::Err);
    assert_eq!(
        kinds(&r),
        [DiagKind::CannotCapture {
            name: k.name("x"),
            binder: x
        }]
    );
}

#[test]
fn test_closure_captures_outer_local() {
    let mut k = Kit::new();
    let one = k.b.int(1);
    let (s, x) = k.let_("x", Some(one));
    let (use_x, p) = k.use_(&["x"]);
    let c = k.closure(&[], use_x);
    let body = k.block(&[s], Some(c));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean());
    assert_eq!(res(&r, 0, p).0, Res::Local(x));
}

#[test]
fn test_module_paths_and_privacy() {
    // mod m { pub fn f() {}  fn secret() {} }  fn main() { (m::f, m::secret, m::nope) }
    let mut k = Kit::new();
    let fb = k.block(&[], None);
    let f = k.func_vis("f", &[], fb, Vis::Public);
    let sb = k.block(&[], None);
    let secret = k.func("secret", &[], sb);
    let m = k.module("m", &[f, secret], Vis::Private);
    let (a, pa) = k.use_(&["m", "f"]);
    let (b2, pb) = k.use_(&["m", "secret"]);
    let (c, pc) = k.use_(&["m", "nope"]);
    let t = k.tuple(&[a, b2, c]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[m, main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, pa).0, item_res(0, f));
    // Private access keeps the resolution and reports once.
    assert_eq!(res(&r, 0, pb).0, item_res(0, secret));
    assert_eq!(res(&r, 0, pc).0, Res::Err);
    let ks = kinds(&r);
    assert!(matches!(
        ks[0],
        DiagKind::Private {
            vis: Vis::Private,
            ..
        }
    ));
    assert!(matches!(
        ks[1],
        DiagKind::Unresolved {
            container: Some(_),
            ..
        }
    ));
    assert_eq!(ks.len(), 2);
}

#[test]
fn test_private_items_visible_to_child_modules() {
    // fn helper() {}  mod child { fn g() { super::helper } }
    let mut k = Kit::new();
    let hb = k.block(&[], None);
    let helper = k.func("helper", &[], hb);
    let (use_h, p) = k.use_root(&["helper"], PathRoot::Super(1));
    let gb = k.block(&[], Some(use_h));
    let g = k.func("g", &[], gb);
    let child = k.module("child", &[g], Vis::Private);
    let hir = k.finish(&[helper, child]);
    let r = resolve_lang::resolve(hir.clone(), &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p).0, item_res(0, helper));
    // Without the descendant rule the access is private.
    let strict = Policy::new().with_visibility(true, false);
    let r = Resolver::new(strict).resolve(hir, &k.names).unwrap();
    assert!(matches!(kinds(&r)[..], [DiagKind::Private { .. }]));
}

#[test]
fn test_isolated_module_does_not_see_outer_items() {
    // fn helper() {}  mod child { fn g() { helper } }
    let mut k = Kit::new();
    let hb = k.block(&[], None);
    let helper = k.func("helper", &[], hb);
    let (use_h, p) = k.use_(&["helper"]);
    let gb = k.block(&[], Some(use_h));
    let g = k.func("g", &[], gb);
    let child = k.module("child", &[g], Vis::Private);
    let hir = k.finish(&[helper, child]);
    let r = resolve_lang::resolve(hir.clone(), &k.names).unwrap();
    assert_eq!(res(&r, 0, p).0, Res::Err);
    let lexical = Policy::new().with_module_scope(resolve_lang::ModuleScope::Lexical);
    let r = Resolver::new(lexical).resolve(hir, &k.names).unwrap();
    assert!(r.is_clean());
    assert_eq!(res(&r, 0, p).0, item_res(0, helper));
}

#[test]
fn test_super_beyond_root_and_self_module() {
    let mut k = Kit::new();
    let (u1, p1) = k.use_root(&["x"], PathRoot::Super(1));
    let (u2, p2) = k.use_root(&["main"], PathRoot::SelfModule);
    let t = k.tuple(&[u1, u2]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p1).0, Res::Err);
    assert_eq!(res(&r, 0, p2).0, item_res(0, main));
    assert_eq!(kinds(&r), [DiagKind::SuperBeyondRoot { levels: 1 }]);
}

#[test]
fn test_sum_variants_and_type_directed_rest() {
    // enum Shape { Circle(..), Empty }  fn main() { (Shape::Circle, Shape::new, Shape::Empty::x) }
    let mut k = Kit::new();
    let (shape, vs) = k.sum("Shape", &[("Circle", false), ("Empty", true)], Vis::Private);
    let (a, pa) = k.use_(&["Shape", "Circle"]);
    let (b2, pb) = k.use_(&["Shape", "new"]);
    let (c, pc) = k.use_(&["Shape", "Empty", "x"]);
    let t = k.tuple(&[a, b2, c]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[shape, main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, pa), (variant_res(0, vs[0]), 0));
    assert_eq!(res(&r, 0, pb), (item_res(0, shape), 1));
    assert_eq!(res(&r, 0, pc).0, Res::Err);
    assert!(matches!(
        kinds(&r)[..],
        [DiagKind::NotAContainer {
            found: DefKind::Variant { .. },
            ..
        }]
    ));
}

#[test]
fn test_function_used_as_type_is_wrong_kind() {
    let mut k = Kit::new();
    let fb = k.block(&[], None);
    let f = k.func("f", &[], fb);
    let (ty, p) = k.ty(&["f"]);
    let g = k.item(
        "C",
        hir_lang::ItemKind::Alias {
            generics: hir_lang::Generics::default(),
            ty,
        },
        Vis::Private,
    );
    let hir = k.finish(&[f, g]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p).0, Res::Err);
    assert!(matches!(
        kinds(&r)[..],
        [DiagKind::WrongKind {
            found: DefKind::Fn,
            ns: Ns::Type,
            ..
        }]
    ));
}

#[test]
fn test_type_param_prefix_is_partial() {
    // fn f<T>() { T::new }
    let mut k = Kit::new();
    let t = k.binder("T", BinderKind::TypeParam);
    let (e, p) = k.use_(&["T", "new"]);
    let body = k.block(&[], Some(e));
    let f = k.generic_fn("f", &[t], body);
    let hir = k.finish(&[f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p), (Res::Local(t), 1));
}

#[test]
fn test_ident_pattern_matches_constants_and_binds_otherwise() {
    // const N = 1; enum E { A } fn f(v) { match v { N => .., A => .., z => z } }
    let mut k = Kit::new();
    let n = k.constant("N", Vis::Private);
    let (e, _) = k.sum("E", &[("A", true)], Vis::Private);
    let (p, _) = k.param("v");
    let (scrut, _) = k.use_(&["v"]);
    let (pat_n, _, path_n) = k.ident_pat("N");
    let (pat_z, z, path_z) = k.ident_pat("z");
    let b1 = k.b.int(1);
    let (use_z, pz) = k.use_(&["z"]);
    let m = k.matches(scrut, &[(pat_n, b1), (pat_z, use_z)]);
    let body = k.block(&[], Some(m));
    let f = k.func("f", &[p], body);
    let hir = k.finish(&[n, e, f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, path_n).0, item_res(0, n));
    assert_eq!(res(&r, 0, path_z).0, Res::Unresolved);
    assert_eq!(res(&r, 0, pz).0, Res::Local(z));
    assert_eq!(r.units()[0].ident_binds(pat_n), Some(false));
    assert_eq!(r.units()[0].ident_binds(pat_z), Some(true));
}

#[test]
fn test_duplicate_definitions_reported_once_each() {
    let mut k = Kit::new();
    let b1 = k.block(&[], None);
    let f1 = k.func("f", &[], b1);
    let b2 = k.block(&[], None);
    let f2 = k.func("f", &[], b2);
    let (use_f, p) = k.use_(&["f"]);
    let b3 = k.block(&[], Some(use_f));
    let main = k.func("main", &[], b3);
    let hir = k.finish(&[f1, f2, main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(matches!(kinds(&r)[..], [DiagKind::Duplicate { .. }]));
    // The first definition is kept.
    assert_eq!(res(&r, 0, p).0, item_res(0, f1));
}

#[test]
fn test_prelude_and_roots_come_from_env() {
    use resolve_lang::{Export, MapEnv, Namespace};
    let mut k = Kit::new();
    let (int_ty, p_int) = k.ty(&["int"]);
    let (e, p_print) = k.use_(&["print"]);
    let (e2, p_io) = k.use_(&["std", "io", "read"]);
    let t = k.tuple(&[e, e2]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let alias = k.item(
        "I",
        hir_lang::ItemKind::Alias {
            generics: hir_lang::Generics::default(),
            ty: int_ty,
        },
        Vis::Private,
    );
    let hir = k.finish(&[main, alias]);
    let (int, print, std, io, read) = (
        k.name("int"),
        k.name("print"),
        k.name("std"),
        k.name("io"),
        k.name("read"),
    );
    let std_res = Res::Extern(std.sym);
    let io_res = Res::Extern(io.sym);
    let env = MapEnv::new()
        .with_prelude(
            int,
            Namespace::Type,
            Export::new(Res::Prim(hir_lang::Prim::I64), DefKind::Prim),
        )
        .with_prelude(
            print,
            Namespace::Value,
            Export::new(Res::Extern(print.sym), DefKind::Extern),
        )
        .with_root(std, Export::new(std_res, DefKind::Module))
        .with_member(
            std_res,
            io,
            Namespace::Module,
            Export::new(io_res, DefKind::Module),
        )
        .with_member(
            io_res,
            read,
            Namespace::Value,
            Export::new(Res::Extern(read.sym), DefKind::Extern),
        );
    let r = Resolver::new(Policy::new())
        .with_env(&env)
        .resolve(hir, &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p_int).0, Res::Prim(hir_lang::Prim::I64));
    assert_eq!(res(&r, 0, p_print).0, Res::Extern(print.sym));
    assert_eq!(res(&r, 0, p_io).0, Res::Extern(read.sym));
}

#[test]
fn test_already_resolved_paths_are_kept() {
    let mut k = Kit::new();
    let (p, x) = k.param("x");
    let use_x = k.b.use_binder(x);
    let body = k.block(&[], Some(use_x));
    let f = k.func("f", &[p], body);
    let hir = k.finish(&[f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean());
    // Still indexed as a reference.
    let def = r
        .index()
        .def_of(resolve_lang::Target::Local(hir_lang::UnitId::new(0), x))
        .unwrap();
    assert_eq!(r.index().references(def).len(), 1);
}

#[test]
fn test_shadowing_policies() {
    use resolve_lang::Shadowing;
    // fn f(a) { let a = 1; { let a = 2; } }
    let build = || {
        let mut k = Kit::new();
        let (p, _) = k.param("a");
        let one = k.b.int(1);
        let (s1, _) = k.let_("a", Some(one));
        let two = k.b.int(2);
        let (s2, _) = k.let_("a", Some(two));
        let inner = k.block(&[s2], None);
        let s3 = k.stmt(inner);
        let body = k.block(&[s1, s3], None);
        let f = k.func("f", &[p], body);
        let hir = k.finish(&[f]);
        (k, hir)
    };
    let (k, hir) = build();
    assert!(resolve_lang::resolve(hir, &k.names).unwrap().is_clean());
    let (k, hir) = build();
    let r = Resolver::new(Policy::new().with_shadowing(Shadowing::DenyLocals))
        .resolve(hir, &k.names)
        .unwrap();
    assert_eq!(r.diagnostics().len(), 2);
    let (k, hir) = build();
    let r = Resolver::new(Policy::new().with_shadowing(Shadowing::DenySameScope))
        .resolve(hir, &k.names)
        .unwrap();
    // The parameter's scope is the function's, the first `let` is the body
    // block's, the second is the inner block's: no two in one scope.
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
}

#[test]
fn test_qualified_self_trait_prefix() {
    // <T as Tr>::Out  — resolve `Tr`, leave `Out` to the type checker.
    let mut k = Kit::new();
    let tr = k.item(
        "Tr",
        hir_lang::ItemKind::Interface(hir_lang::InterfaceDef::default()),
        Vis::Private,
    );
    let t = k.binder("T", BinderKind::TypeParam);
    let (qty, _) = k.ty(&["T"]);
    let segs = k.segs(&["Tr", "Out"]);
    let path = k.b.path(hir_lang::Path {
        qself: Some(hir_lang::QSelf {
            ty: qty,
            trait_len: 1,
        }),
        ..hir_lang::Path::new(segs, Ns::Type)
    });
    let ty = k.b.ty(hir_lang::Ty::Path(path));
    let gps = k.b.list(&[hir_lang::GenericParam::new(t)]);
    let alias = k.item(
        "A",
        hir_lang::ItemKind::Alias {
            generics: hir_lang::Generics {
                params: gps,
                preds: hir_lang::List::EMPTY,
            },
            ty,
        },
        Vis::Private,
    );
    let hir = k.finish(&[tr, alias]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, path), (item_res(0, tr), 1));
}

#[test]
fn test_result_hir_validates() {
    let mut k = Kit::new();
    let (e, _) = k.use_(&["nothing", "here"]);
    let body = k.block(&[], Some(e));
    let f = k.func("f", &[], body);
    let hir = k.finish(&[f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(r.diagnostics().len(), 1);
    assert!(r.units()[0].hir().validate().is_ok());
}
