//! Imports and multi-unit programs: named, aliased, glob, re-exported,
//! private, cyclic, and across units and the environment.

#![allow(clippy::unwrap_used, clippy::expect_used)]

mod common;

use common::{Kit, item_res, kinds, messages, res, variant_res};
use hir_lang::{PathRoot, Res, Vis};
use resolve_lang::{
    DefKind, DiagKind, Export, MapEnv, Namespace, Policy, Program, Reexport, Resolver,
};

#[test]
fn test_two_units_import_each_other() {
    // unit 1 `a`: use b::helper; pub fn bar() { helper }
    // unit 2 `b`: use a::bar;    pub fn helper() { bar }
    let mut k = Kit::for_unit(1, intern_lang::Interner::new());
    let (imp_a, ip_a) = k.import(&["b", "helper"], None, Vis::Private);
    let (use_helper, p_helper) = k.use_(&["helper"]);
    let body = k.block(&[], Some(use_helper));
    let bar = k.func_vis("bar", &[], body, Vis::Public);
    let hir_a = k.finish(&[imp_a, bar]);
    k.start_unit(2);
    let (imp_b, ip_b) = k.import(&["a", "bar"], None, Vis::Private);
    let (use_bar, p_bar) = k.use_(&["bar"]);
    let body = k.block(&[], Some(use_bar));
    let helper = k.func_vis("helper", &[], body, Vis::Public);
    let hir_b = k.finish(&[imp_b, helper]);
    let (a, b) = (k.name("a"), k.name("b"));
    let mut program = Program::new(Policy::kraken());
    program.add_unit(Some(a), hir_a);
    program.add_unit(Some(b), hir_b);
    let r = program.resolve(&k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 1, p_helper).0, item_res(2, helper));
    assert_eq!(res(&r, 2, p_bar).0, item_res(1, bar));
    assert_eq!(res(&r, 1, ip_a).0, item_res(2, helper));
    assert_eq!(res(&r, 2, ip_b).0, item_res(1, bar));
    // The index sees the cross-unit references.
    let def = r
        .index()
        .def_of(resolve_lang::Target::Def(match item_res(2, helper) {
            Res::Def(d) => d,
            _ => unreachable!(),
        }));
    let refs = r.index().references(def.unwrap());
    assert_eq!(refs.len(), 2, "import segment and use");
}

#[test]
fn test_reexport_chain_and_private_import() {
    // unit 1 `b`: pub fn x() {}
    // unit 2 `a`: pub use b::x as y;  use b::x;   (private)
    // unit 3:     use a::y; use a::x; fn main() { y }
    let mut k = Kit::for_unit(1, intern_lang::Interner::new());
    let body = k.block(&[], None);
    let x = k.func_vis("x", &[], body, Vis::Public);
    let hir_b = k.finish(&[x]);
    k.start_unit(2);
    let (pub_alias, _) = k.import(&["b", "x"], Some("y"), Vis::Public);
    let (priv_imp, _) = k.import(&["b", "x"], None, Vis::Private);
    let hir_a = k.finish(&[pub_alias, priv_imp]);
    k.start_unit(3);
    let (i1, p1) = k.import(&["a", "y"], None, Vis::Private);
    let (i2, p2) = k.import(&["a", "x"], None, Vis::Private);
    let (use_y, py) = k.use_(&["y"]);
    let body = k.block(&[], Some(use_y));
    let main = k.func("main", &[], body);
    let hir_c = k.finish(&[i1, i2, main]);
    let (a, b) = (k.name("a"), k.name("b"));
    let mut program = Program::new(Policy::kraken());
    program.add_unit(Some(b), hir_b);
    program.add_unit(Some(a), hir_a);
    program.add_unit(None, hir_c);
    let r = program.resolve(&k.names).unwrap();
    assert_eq!(res(&r, 3, p1).0, item_res(1, x));
    assert_eq!(res(&r, 3, py).0, item_res(1, x));
    // The private import resolves (for navigation) but is reported.
    assert_eq!(res(&r, 3, p2).0, item_res(1, x));
    assert!(
        matches!(
            kinds(&r)[..],
            [DiagKind::Private {
                vis: Vis::Private,
                ..
            }]
        ),
        "{:?}",
        messages(&r, &k.names)
    );
}

#[test]
fn test_python_style_import_does_not_find_itself() {
    // import os; fn main() { os::getcwd }   with `os` an environment root.
    let mut k = Kit::new();
    let (imp, ip) = k.import(&["os"], None, Vis::Private);
    let (e, p) = k.use_(&["os", "getcwd"]);
    let body = k.block(&[], Some(e));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[imp, main]);
    let (os, getcwd) = (k.name("os"), k.name("getcwd"));
    let os_res = Res::Extern(os.sym);
    let env = MapEnv::new()
        .with_root(os, Export::new(os_res, DefKind::Module))
        .with_member(
            os_res,
            getcwd,
            Namespace::Value,
            Export::new(Res::Extern(getcwd.sym), DefKind::Extern),
        );
    let r = Resolver::new(Policy::python())
        .with_env(&env)
        .resolve(hir, &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, ip).0, os_res);
    assert_eq!(res(&r, 0, p).0, Res::Extern(getcwd.sym));
}

#[test]
fn test_glob_imports_and_shadowing_by_definitions() {
    // mod m { pub fn f() {} pub fn g() {} }  use m::*;  fn g() {}  fn main() { (f, g) }
    let mut k = Kit::new();
    let b1 = k.block(&[], None);
    let f = k.func_vis("f", &[], b1, Vis::Public);
    let b2 = k.block(&[], None);
    let mg = k.func_vis("g", &[], b2, Vis::Public);
    let m = k.module("m", &[f, mg], Vis::Private);
    let (glob, gp) = k.glob(&["m"], Vis::Private);
    let b3 = k.block(&[], None);
    let g = k.func("g", &[], b3);
    let (uf, pf) = k.use_(&["f"]);
    let (ug, pg) = k.use_(&["g"]);
    let t = k.tuple(&[uf, ug]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[m, glob, g, main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, gp).0, item_res(0, m));
    assert_eq!(res(&r, 0, pf).0, item_res(0, f));
    assert_eq!(res(&r, 0, pg).0, item_res(0, g));
}

#[test]
fn test_ambiguous_globs_reported_at_use() {
    // mod a { pub fn x() {} } mod b { pub fn x() {} } use a::*; use b::*; fn main() { x }
    let mut k = Kit::new();
    let b1 = k.block(&[], None);
    let ax = k.func_vis("x", &[], b1, Vis::Public);
    let a = k.module("a", &[ax], Vis::Private);
    let b2 = k.block(&[], None);
    let bx = k.func_vis("x", &[], b2, Vis::Public);
    let b = k.module("b", &[bx], Vis::Private);
    let (g1, _) = k.glob(&["a"], Vis::Private);
    let (g2, _) = k.glob(&["b"], Vis::Private);
    let (ux, px) = k.use_(&["x"]);
    let body = k.block(&[], Some(ux));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[a, b, g1, g2, main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, px).0, Res::Err);
    assert!(
        matches!(kinds(&r)[..], [DiagKind::AmbiguousGlob { .. }]),
        "{:?}",
        messages(&r, &k.names)
    );
}

#[test]
fn test_same_item_through_two_globs_is_not_ambiguous() {
    // mod a { pub fn x() {} } mod b { pub use super::a::x; } use a::*; use b::*; x
    let mut k = Kit::new();
    let b1 = k.block(&[], None);
    let ax = k.func_vis("x", &[], b1, Vis::Public);
    let a = k.module("a", &[ax], Vis::Private);
    let (reexp, _) = k.import_root(&["a", "x"], PathRoot::Super(1), Vis::Public);
    let b = k.module("b", &[reexp], Vis::Private);
    let (g1, _) = k.glob(&["a"], Vis::Private);
    let (g2, _) = k.glob(&["b"], Vis::Private);
    let (ux, px) = k.use_(&["x"]);
    let body = k.block(&[], Some(ux));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[a, b, g1, g2, main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, px).0, item_res(0, ax));
}

#[test]
fn test_glob_cycle_between_modules() {
    // mod a { pub use super::b::*; pub fn x() {} }
    // mod b { pub use super::a::*; pub fn y() {} }
    // fn main() { (a::y, b::x) }
    let mut k = Kit::new();
    let (ga, _) = {
        let path = k.path_root(&["b"], hir_lang::Ns::Import, PathRoot::Super(1));
        let item = k.b.item(
            hir_lang::Item::new(None, hir_lang::ItemKind::Import { path, glob: true })
                .with_vis(Vis::Public),
        );
        (item, path)
    };
    let b1 = k.block(&[], None);
    let x = k.func_vis("x", &[], b1, Vis::Public);
    let a = k.module("a", &[ga, x], Vis::Private);
    let (gb, _) = {
        let path = k.path_root(&["a"], hir_lang::Ns::Import, PathRoot::Super(1));
        let item = k.b.item(
            hir_lang::Item::new(None, hir_lang::ItemKind::Import { path, glob: true })
                .with_vis(Vis::Public),
        );
        (item, path)
    };
    let b2 = k.block(&[], None);
    let y = k.func_vis("y", &[], b2, Vis::Public);
    let b = k.module("b", &[gb, y], Vis::Private);
    let (ay, pay) = k.use_(&["a", "y"]);
    let (bx, pbx) = k.use_(&["b", "x"]);
    let t = k.tuple(&[ay, bx]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[a, b, main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, pay).0, item_res(0, y));
    assert_eq!(res(&r, 0, pbx).0, item_res(0, x));
}

#[test]
fn test_import_cycle_is_reported() {
    // use self::q as p;  use self::p as q;
    let mut k = Kit::new();
    let (i1, p1) = {
        let path = k.path_root(&["q"], hir_lang::Ns::Import, PathRoot::SelfModule);
        let n = k.name("p");
        (
            k.b.item(hir_lang::Item::new(
                Some(n),
                hir_lang::ItemKind::Import { path, glob: false },
            )),
            path,
        )
    };
    let (i2, p2) = {
        let path = k.path_root(&["p"], hir_lang::Ns::Import, PathRoot::SelfModule);
        let n = k.name("q");
        (
            k.b.item(hir_lang::Item::new(
                Some(n),
                hir_lang::ItemKind::Import { path, glob: false },
            )),
            path,
        )
    };
    let (up, pp) = k.use_(&["p"]);
    let body = k.block(&[], Some(up));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[i1, i2, main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p1).0, Res::Err);
    assert_eq!(res(&r, 0, p2).0, Res::Err);
    assert_eq!(res(&r, 0, pp).0, Res::Err);
    let ks = kinds(&r);
    assert!(
        ks.iter().any(|k| matches!(k, DiagKind::ImportCycle { .. })),
        "{:?}",
        messages(&r, &k.names)
    );
    assert!(
        ks.iter()
            .any(|k| matches!(k, DiagKind::BrokenImport { .. }))
    );
    assert_eq!(ks.len(), 3, "{:?}", messages(&r, &k.names));
}

#[test]
fn test_unresolved_import_suggests() {
    let mut k = Kit::new();
    let b1 = k.block(&[], None);
    let helper = k.func_vis("helper", &[], b1, Vis::Public);
    let m = k.module("m", &[helper], Vis::Private);
    let (imp, _) = k.import(&["m", "hepler"], None, Vis::Private);
    let hir = k.finish(&[m, imp]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    let ms = messages(&r, &k.names);
    assert_eq!(ms, ["cannot find `hepler` in `m`; did you mean `helper`?"]);
}

#[test]
fn test_glob_of_sum_variants() {
    // enum Shape { Circle, Square } use Shape::*; fn main() { Circle }
    let mut k = Kit::new();
    let (shape, vs) = k.sum("Shape", &[("Circle", true), ("Square", true)], Vis::Private);
    let (g, _) = k.glob(&["Shape"], Vis::Private);
    let (uc, pc) = k.use_(&["Circle"]);
    let body = k.block(&[], Some(uc));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[shape, g, main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, pc).0, variant_res(0, vs[0]));
}

#[test]
fn test_glob_of_environment_container() {
    let mut k = Kit::new();
    let (g, _) = k.glob(&["std"], Vis::Private);
    let (ue, pe) = k.use_(&["print"]);
    let body = k.block(&[], Some(ue));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[g, main]);
    let (std, print) = (k.name("std"), k.name("print"));
    let std_res = Res::Extern(std.sym);
    let env = MapEnv::new()
        .with_root(std, Export::new(std_res, DefKind::Module))
        .with_member(
            std_res,
            print,
            Namespace::Value,
            Export::new(Res::Extern(print.sym), DefKind::Extern),
        );
    let r = Resolver::new(Policy::new())
        .with_env(&env)
        .resolve(hir, &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, pe).0, Res::Extern(print.sym));
}

#[test]
fn test_package_visibility_across_units() {
    let build = |same_package: bool| {
        let mut k = Kit::for_unit(1, intern_lang::Interner::new());
        let body = k.block(&[], None);
        let f = k.func_vis("f", &[], body, Vis::Package);
        let hir1 = k.finish(&[f]);
        k.start_unit(2);
        let (e, p) = k.use_(&["lib", "f"]);
        let body = k.block(&[], Some(e));
        let main = k.func("main", &[], body);
        let hir2 = k.finish(&[main]);
        let lib = k.name("lib");
        let mut program = Program::new(Policy::new());
        program.add_unit_in(1, Some(lib), hir1);
        program.add_unit_in(if same_package { 1 } else { 2 }, None, hir2);
        let r = program.resolve(&k.names).unwrap();
        (r, p, f)
    };
    let (r, p, f) = build(true);
    assert!(r.is_clean());
    assert_eq!(res(&r, 2, p).0, item_res(1, f));
    let (r, p, f) = build(false);
    assert_eq!(res(&r, 2, p).0, item_res(1, f));
    assert!(matches!(
        kinds(&r)[..],
        [DiagKind::Private {
            vis: Vis::Package,
            ..
        }]
    ));
}

#[test]
fn test_broken_import_name_reported_at_use() {
    let mut k = Kit::new();
    let (imp, _) = k.import(&["nowhere", "thing"], None, Vis::Private);
    let (u, p) = k.use_(&["thing"]);
    let body = k.block(&[], Some(u));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[imp, main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p).0, Res::Err);
    let ks = kinds(&r);
    assert!(matches!(ks[0], DiagKind::Unresolved { .. }));
    assert!(matches!(ks[1], DiagKind::BrokenImport { .. }));
}

#[test]
fn test_policy_disables_globs_and_aliases() {
    let mut k = Kit::new();
    let b1 = k.block(&[], None);
    let f = k.func_vis("f", &[], b1, Vis::Public);
    let m = k.module("m", &[f], Vis::Private);
    let (g, _) = k.glob(&["m"], Vis::Private);
    let (a, pa) = k.import(&["m", "f"], Some("ff"), Vis::Private);
    let hir = k.finish(&[m, g, a]);
    let policy = Policy::new().with_imports(false, false, Reexport::AsDeclared);
    let r = Resolver::new(policy).resolve(hir, &k.names).unwrap();
    let ks = kinds(&r);
    assert!(ks.contains(&DiagKind::GlobsUnsupported));
    assert!(ks.contains(&DiagKind::AliasesUnsupported));
    // The aliased import still resolves.
    assert_eq!(res(&r, 0, pa).0, item_res(0, f));
}

#[test]
fn test_duplicate_import_and_definition() {
    let mut k = Kit::new();
    let b1 = k.block(&[], None);
    let f = k.func_vis("f", &[], b1, Vis::Public);
    let m = k.module("m", &[f], Vis::Private);
    let (imp, _) = k.import(&["m", "f"], None, Vis::Private);
    let b2 = k.block(&[], None);
    let local_f = k.func("f", &[], b2);
    let hir = k.finish(&[m, imp, local_f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(
        matches!(kinds(&r)[..], [DiagKind::Duplicate { .. }]),
        "{:?}",
        messages(&r, &k.names)
    );
}

#[test]
fn test_python_reexports_imports_always() {
    // unit `b`: from c import x   (private by default, but Python exports it)
    // unit 3:   from b import x
    let mut k = Kit::for_unit(1, intern_lang::Interner::new());
    let body = k.block(&[], None);
    let x = k.func_vis("x", &[], body, Vis::Public);
    let hir_c = k.finish(&[x]);
    k.start_unit(2);
    let (imp, _) = k.import(&["c", "x"], None, Vis::Private);
    let hir_b = k.finish(&[imp]);
    k.start_unit(3);
    let (imp3, p3) = k.import(&["b", "x"], None, Vis::Private);
    let hir_3 = k.finish(&[imp3]);
    let (b, c) = (k.name("b"), k.name("c"));
    let mut program = Program::new(Policy::python());
    program.add_unit(Some(c), hir_c);
    program.add_unit(Some(b), hir_b);
    program.add_unit(None, hir_3);
    let r = program.resolve(&k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 3, p3).0, item_res(1, x));
}

#[test]
fn test_block_scoped_import() {
    // mod m { pub fn f() {} }  fn main() { use m::f; f }
    let mut k = Kit::new();
    let b1 = k.block(&[], None);
    let f = k.func_vis("f", &[], b1, Vis::Public);
    let m = k.module("m", &[f], Vis::Private);
    let (imp, _) = k.import(&["m", "f"], None, Vis::Private);
    let si = k.item_stmt(imp);
    let (uf, pf) = k.use_(&["f"]);
    let body = k.block(&[si], Some(uf));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[m, main]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, pf).0, item_res(0, f));
}

#[test]
fn test_glob_budget_is_enforced() {
    // Ten modules each glob-importing all others, each defining one name.
    let mut k = Kit::new();
    let mut mods = Vec::new();
    for i in 0..10 {
        let mut items = Vec::new();
        for j in 0..10 {
            if i != j {
                let path = k.path_root(
                    &[&format!("m{j}")],
                    hir_lang::Ns::Import,
                    PathRoot::Super(1),
                );
                items.push(
                    k.b.item(
                        hir_lang::Item::new(None, hir_lang::ItemKind::Import { path, glob: true })
                            .with_vis(Vis::Public),
                    ),
                );
            }
        }
        let body = k.block(&[], None);
        items.push(k.func_vis(&format!("f{i}"), &[], body, Vis::Public));
        mods.push(k.module(&format!("m{i}"), &items, Vis::Private));
    }
    let hir = k.finish(&mods);
    let tight = resolve_lang::Budget::default().with_glob_bindings(20);
    let err = Resolver::new(Policy::new())
        .with_budget(tight)
        .resolve(hir.clone(), &k.names)
        .unwrap_err();
    assert_eq!(
        err,
        resolve_lang::ResolveError::BudgetExceeded {
            limit: resolve_lang::Limit::GlobBindings
        }
    );
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
}
