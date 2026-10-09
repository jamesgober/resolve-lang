//! Language policies: PHP, Python, and Kraken-style scoping differences on
//! the same kinds of programs, plus class members and mixins.

#![allow(clippy::unwrap_used, clippy::expect_used)]

mod common;

use common::{Kit, item_res, kinds, messages, res};
use hir_lang::{Ident, ItemKind, MixinAction, MixinRule, PathRoot, Res, Span, Stmt, Vis};
use resolve_lang::{DiagKind, Namespace, Policy, Resolver};

// ------------------------------------------------------------------- PHP

#[test]
fn test_php_function_declared_in_a_block_is_module_wide() {
    // function main() { if (..) { function late() {} } }  function other() { late }
    let mut k = Kit::new();
    let lb = k.block(&[], None);
    let late = k.func("late", &[], lb);
    let s = k.item_stmt(late);
    let inner = k.block(&[s], None);
    let st = k.stmt(inner);
    let mb = k.block(&[st], None);
    let main = k.func("main", &[], mb);
    let (u, p) = k.use_(&["late"]);
    let ob = k.block(&[], Some(u));
    let other = k.func("other", &[], ob);
    let hir = k.finish(&[main, other]);
    let r = Resolver::new(Policy::php())
        .resolve(hir.clone(), &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p).0, item_res(0, late));
    // Kraken: the block item is local to its block.
    let r = Resolver::new(Policy::kraken())
        .resolve(hir, &k.names)
        .unwrap();
    assert_eq!(res(&r, 0, p).0, Res::Err);
}

#[test]
fn test_php_global_declaration() {
    // function f() { global $config; global $fresh; }   with no module global named fresh
    let mut k = Kit::new();
    let cfg = k.global("config", None, Vis::Private);
    let b1 = k.binder("config", hir_lang::BinderKind::Local);
    let path1 = k.path(&["config"], hir_lang::Ns::Value);
    let s1 = k.b.stmt(Stmt::Global {
        binder: b1,
        path: path1,
    });
    let b2 = k.binder("fresh", hir_lang::BinderKind::Local);
    let path2 = k.path(&["fresh"], hir_lang::Ns::Value);
    let s2 = k.b.stmt(Stmt::Global {
        binder: b2,
        path: path2,
    });
    let body = k.block(&[s1, s2], None);
    let f = k.func("f", &[], body);
    let hir = k.finish(&[cfg, f]);
    let r = Resolver::new(Policy::php())
        .resolve(hir.clone(), &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, path1).0, item_res(0, cfg));
    assert_eq!(res(&r, 0, path2).0, Res::Extern(k.name("fresh").sym));
    // Without implicit globals, the unknown one is an error.
    let r = Resolver::new(Policy::kraken())
        .resolve(hir, &k.names)
        .unwrap();
    assert!(matches!(kinds(&r)[..], [DiagKind::Unresolved { .. }]));
}

/// class Base { const B = 1; function hello() {} }
/// class Child extends Base { const C = 2; function m() { (self::C, parent::hello, static::C, self::B, C) } }
fn class_program(k: &mut Kit) -> ClassProgram {
    let b_const = k.constant("B", Vis::Public);
    let hb = k.block(&[], None);
    let hello = k.func_vis("hello", &[], hb, Vis::Protected);
    let base = k.class("Base", &[], &[b_const, hello], false);
    let c_const = k.constant("C", Vis::Private);
    let (e1, self_c) = k.use_root(&["C"], PathRoot::SelfType);
    let (e2, parent_hello) = k.use_root(&["hello"], PathRoot::ParentType);
    let (e3, static_c) = k.use_root(&["C"], PathRoot::StaticType);
    let (e4, self_b) = k.use_root(&["B"], PathRoot::SelfType);
    let (e5, bare_c) = k.use_(&["C"]);
    let t = k.tuple(&[e1, e2, e3, e4, e5]);
    let mb = k.block(&[], Some(t));
    let m = k.func_vis("m", &[], mb, Vis::Public);
    let (base_ty, _) = k.ty(&["Base"]);
    let child = k.class("Child", &[base_ty], &[c_const, m], false);
    // Outside any class: Child::C (private) and Child::hello (protected).
    let (o1, out_c) = k.use_(&["Child", "C"]);
    let (o2, out_hello) = k.use_(&["Child", "hello"]);
    let (o3, out_b) = k.use_(&["Child", "B"]);
    let t = k.tuple(&[o1, o2, o3]);
    let fb = k.block(&[], Some(t));
    let outside = k.func("outside", &[], fb);
    let hir = k.finish(&[base, child, outside]);
    ClassProgram {
        hir,
        hello,
        b_const,
        c_const,
        self_c,
        parent_hello,
        static_c,
        self_b,
        bare_c,
        out_c,
        out_hello,
        out_b,
    }
}

struct ClassProgram {
    hir: hir_lang::Hir,
    hello: hir_lang::ItemId,
    b_const: hir_lang::ItemId,
    c_const: hir_lang::ItemId,
    self_c: hir_lang::PathId,
    parent_hello: hir_lang::PathId,
    static_c: hir_lang::PathId,
    self_b: hir_lang::PathId,
    bare_c: hir_lang::PathId,
    out_c: hir_lang::PathId,
    out_hello: hir_lang::PathId,
    out_b: hir_lang::PathId,
}

#[test]
fn test_php_type_roots_and_member_access() {
    let mut k = Kit::new();
    let c = class_program(&mut k);
    let r = Resolver::new(Policy::php())
        .resolve(c.hir, &k.names)
        .unwrap();
    assert_eq!(res(&r, 0, c.self_c), (item_res(0, c.c_const), 0));
    assert_eq!(res(&r, 0, c.parent_hello), (item_res(0, c.hello), 0));
    // Late static binding: left for run time.
    assert_eq!(res(&r, 0, c.static_c), (Res::Unresolved, 1));
    // Inherited through the base.
    assert_eq!(res(&r, 0, c.self_b), (item_res(0, c.b_const), 0));
    // PHP class members are not visible unqualified.
    assert_eq!(res(&r, 0, c.bare_c).0, Res::Err);
    // From outside: public resolves; private and protected resolve but are reported.
    assert_eq!(res(&r, 0, c.out_b), (item_res(0, c.b_const), 0));
    assert_eq!(res(&r, 0, c.out_c), (item_res(0, c.c_const), 0));
    assert_eq!(res(&r, 0, c.out_hello), (item_res(0, c.hello), 0));
    let ks = kinds(&r);
    assert_eq!(ks.len(), 3, "{:?}", messages(&r, &k.names));
    assert!(matches!(ks[0], DiagKind::Unresolved { .. }));
    assert!(matches!(
        ks[1],
        DiagKind::Private {
            vis: Vis::Private,
            ..
        }
    ));
    assert!(matches!(
        ks[2],
        DiagKind::Private {
            vis: Vis::Protected,
            ..
        }
    ));
}

#[test]
fn test_kraken_class_members_are_lexical() {
    let mut k = Kit::new();
    let c = class_program(&mut k);
    let r = Resolver::new(Policy::kraken())
        .resolve(c.hir, &k.names)
        .unwrap();
    // `C` is visible unqualified in the method.
    assert_eq!(res(&r, 0, c.bare_c).0, item_res(0, c.c_const));
    // Kraken has no `parent::` or `static::`.
    let ks = kinds(&r);
    assert!(ks.contains(&DiagKind::RootUnsupported {
        root: PathRoot::ParentType
    }));
    assert!(ks.contains(&DiagKind::RootUnsupported {
        root: PathRoot::StaticType
    }));
}

#[test]
fn test_self_outside_class_and_parent_without_base() {
    let mut k = Kit::new();
    let (e1, p1) = k.use_root(&["x"], PathRoot::SelfType);
    let fb = k.block(&[], Some(e1));
    let f = k.func("f", &[], fb);
    let (e2, p2) = k.use_root(&["x"], PathRoot::ParentType);
    let mb = k.block(&[], Some(e2));
    let m = k.func("m", &[], mb);
    let class = k.class("Lonely", &[], &[m], false);
    let hir = k.finish(&[f, class]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p1).0, Res::Err);
    assert_eq!(res(&r, 0, p2).0, Res::Err);
    assert_eq!(
        kinds(&r),
        [
            DiagKind::OutsideType {
                root: PathRoot::SelfType
            },
            DiagKind::NoParent
        ]
    );
}

fn rule(k: &mut Kit, from: Option<&str>, method: &str, action: MixinAction) -> MixinRule {
    let from = from.map(|f| k.ty(&[f]).0);
    MixinRule {
        method: Ident::new(k.name(method).sym, Span::empty(0)),
        from,
        action,
    }
}

#[test]
fn test_php_mixins_with_insteadof_and_alias() {
    // trait A { function hi() {} function a() {} }  trait B { function hi() {} }
    // class C { use A, B { A::hi insteadof B; B::hi as protected bhi; } function m() { (self::hi, self::bhi, self::a) } }
    let mut k = Kit::new();
    let hb = k.block(&[], None);
    let a_hi = k.func_vis("hi", &[], hb, Vis::Public);
    let ab = k.block(&[], None);
    let a_a = k.func_vis("a", &[], ab, Vis::Public);
    let ta = k.class("A", &[], &[a_hi, a_a], true);
    let hb2 = k.block(&[], None);
    let b_hi = k.func_vis("hi", &[], hb2, Vis::Public);
    let tb = k.class("B", &[], &[b_hi], true);
    let (ty_a, _) = k.ty(&["A"]);
    let (ty_b, _) = k.ty(&["B"]);
    let (other_b, _) = k.ty(&["B"]);
    let others = k.b.list(&[other_b]);
    let r1 = rule(&mut k, Some("A"), "hi", MixinAction::Insteadof(others));
    let alias = k.ident("bhi");
    let r2 = rule(
        &mut k,
        Some("B"),
        "hi",
        MixinAction::Alias {
            name: Some(alias),
            vis: Some(Vis::Protected),
        },
    );
    let mu = k.mixin_use(&[ty_a, ty_b], &[r1, r2]);
    let (e1, p_hi) = k.use_root(&["hi"], PathRoot::SelfType);
    let (e2, p_bhi) = k.use_root(&["bhi"], PathRoot::SelfType);
    let (e3, p_a) = k.use_root(&["a"], PathRoot::SelfType);
    let t = k.tuple(&[e1, e2, e3]);
    let mb = k.block(&[], Some(t));
    let m = k.func_vis("m", &[], mb, Vis::Public);
    let c = k.class("C", &[], &[mu, m], false);
    let hir = k.finish(&[ta, tb, c]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p_hi).0, item_res(0, a_hi));
    assert_eq!(res(&r, 0, p_bhi).0, item_res(0, b_hi));
    assert_eq!(res(&r, 0, p_a).0, item_res(0, a_a));
    let members = r.units()[0].members(c).unwrap();
    let mut names: Vec<String> = members
        .iter()
        .map(|m| k.names.resolve(m.name.sym).unwrap().to_string())
        .collect();
    names.sort();
    assert_eq!(names, ["a", "bhi", "hi", "m"]);
    let bhi = members.iter().find(|m| m.name == k.name("bhi")).unwrap();
    assert_eq!(bhi.vis, Vis::Protected);
    assert_eq!(bhi.namespace, Namespace::Value);
    assert!(bhi.mixin.is_some());
}

#[test]
fn test_php_mixin_conflict_cycle_and_unknown_member() {
    // trait A { function hi() {} }  trait B { function hi() {} }  class C { use A, B; }
    // trait L { use L; }   class D { use A { nope as x; } }   class E { use C; } (C not a mixin)
    let mut k = Kit::new();
    let hb = k.block(&[], None);
    let a_hi = k.func_vis("hi", &[], hb, Vis::Public);
    let ta = k.class("A", &[], &[a_hi], true);
    let hb2 = k.block(&[], None);
    let b_hi = k.func_vis("hi", &[], hb2, Vis::Public);
    let tb = k.class("B", &[], &[b_hi], true);
    let (ty_a, _) = k.ty(&["A"]);
    let (ty_b, _) = k.ty(&["B"]);
    let mu = k.mixin_use(&[ty_a, ty_b], &[]);
    let c = k.class("C", &[], &[mu], false);
    let (ty_l, _) = k.ty(&["L"]);
    let mul = k.mixin_use(&[ty_l], &[]);
    let tl = k.class("L", &[], &[mul], true);
    let (ty_a2, _) = k.ty(&["A"]);
    let alias = k.ident("x");
    let bad = rule(
        &mut k,
        None,
        "nope",
        MixinAction::Alias {
            name: Some(alias),
            vis: None,
        },
    );
    let mud = k.mixin_use(&[ty_a2], &[bad]);
    let d = k.class("D", &[], &[mud], false);
    let (ty_c, _) = k.ty(&["C"]);
    let mue = k.mixin_use(&[ty_c], &[]);
    let e = k.class("E", &[], &[mue], false);
    let hir = k.finish(&[ta, tb, c, tl, d, e]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    let ks = kinds(&r);
    assert!(
        ks.iter()
            .any(|k| matches!(k, DiagKind::MixinConflict { .. })),
        "{:?}",
        messages(&r, &k.names)
    );
    assert!(ks.contains(&DiagKind::MixinCycle));
    assert!(
        ks.iter()
            .any(|k| matches!(k, DiagKind::UnknownMixinMember { .. }))
    );
    assert!(ks.iter().any(|k| matches!(k, DiagKind::NotAMixin { .. })));
    // C keeps the first mixin's `hi`.
    let hi = r.units()[0]
        .members(c)
        .unwrap()
        .iter()
        .find(|m| m.name == k.name("hi"))
        .unwrap();
    assert_eq!(hi.res, item_res(0, a_hi));
}

// ---------------------------------------------------------------- Python

#[test]
fn test_python_class_body_visible_to_initializers_not_methods() {
    // class K:
    //     x = 1
    //     y = x        # sees x
    //     def m(self): return x   # does not (LEGB skips class scope)
    let mut k = Kit::new();
    let one = k.b.int(1);
    let x = k.global("x", Some(one), Vis::Public);
    let (ux, p_init) = k.use_(&["x"]);
    let y = k.global("y", Some(ux), Vis::Public);
    let (ux2, p_method) = k.use_(&["x"]);
    let mb = k.block(&[], Some(ux2));
    let m = k.func_vis("m", &[], mb, Vis::Public);
    let class = k.class("K", &[], &[x, y, m], false);
    let hir = k.finish(&[class]);
    let r = Resolver::new(Policy::python())
        .resolve(hir.clone(), &k.names)
        .unwrap();
    assert_eq!(res(&r, 0, p_init).0, item_res(0, x));
    assert_eq!(res(&r, 0, p_method).0, Res::Err);
    assert_eq!(r.diagnostics().len(), 1, "{:?}", messages(&r, &k.names));
    // Kraken sees class members everywhere in the class.
    let r = Resolver::new(Policy::kraken())
        .resolve(hir, &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p_method).0, item_res(0, x));
}

#[test]
fn test_python_module_global_seen_by_enclosing_fn_and_class_in_between() {
    // x = 1 (module)   class K: x = 2; def m(self): return x  -> module x
    let mut k = Kit::new();
    let one = k.b.int(1);
    let mx = k.global("x", Some(one), Vis::Public);
    let two = k.b.int(2);
    let kx = k.global("x", Some(two), Vis::Public);
    let (ux, p) = k.use_(&["x"]);
    let mb = k.block(&[], Some(ux));
    let m = k.func_vis("m", &[], mb, Vis::Public);
    let class = k.class("K", &[], &[kx, m], false);
    let hir = k.finish(&[mx, class]);
    let r = Resolver::new(Policy::python())
        .resolve(hir, &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p).0, item_res(0, mx));
}

#[test]
fn test_python_redefinition_last_wins_and_one_namespace() {
    // def f(): ...   def f(): ...   class f: ...   use f
    let mut k = Kit::new();
    let b1 = k.block(&[], None);
    let f1 = k.func("f", &[], b1);
    let b2 = k.block(&[], None);
    let f2 = k.func("f", &[], b2);
    let (u, p) = k.use_(&["f"]);
    let mb = k.block(&[], Some(u));
    let main = k.func("main", &[], mb);
    let hir = k.finish(&[f1, f2, main]);
    let r = Resolver::new(Policy::python())
        .resolve(hir.clone(), &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p).0, item_res(0, f2));
    let r = Resolver::new(Policy::kraken())
        .resolve(hir, &k.names)
        .unwrap();
    assert_eq!(res(&r, 0, p).0, item_res(0, f1));
    assert!(matches!(kinds(&r)[..], [DiagKind::Duplicate { .. }]));
}

#[test]
fn test_merged_namespaces_make_type_and_value_collide() {
    // fn T() {}  record T  -> separate tables in Kraken would still collide on
    // Value (records occupy value too); with records type-only they coexist.
    let mut k = Kit::new();
    let b1 = k.block(&[], None);
    let f = k.func("T", &[], b1);
    let rec = k.record("T", false, Vis::Private);
    let hir = k.finish(&[f, rec]);
    let type_only = Policy::new().with_occupies(
        resolve_lang::ItemClass::Record,
        resolve_lang::NsSet::single(Namespace::Type),
    );
    let r = Resolver::new(type_only)
        .resolve(hir.clone(), &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    let merged = type_only.with_merge(Namespace::Type, Namespace::Value);
    let r = Resolver::new(merged).resolve(hir, &k.names).unwrap();
    assert!(matches!(kinds(&r)[..], [DiagKind::Duplicate { .. }]));
}

#[test]
fn test_inherited_member_lookup_through_long_chain() {
    // class C0 { const K } class C1 extends C0 ... class C499 extends C498 { m() { self::K } }
    let mut k = Kit::new();
    let kc = k.constant("K", Vis::Public);
    let mut items = vec![k.class("C0", &[], &[kc], false)];
    let mut last_path = None;
    for i in 1..500 {
        let (base, _) = k.ty(&[&format!("C{}", i - 1)]);
        let mut members = Vec::new();
        if i == 499 {
            let (e, p) = k.use_root(&["K"], PathRoot::SelfType);
            last_path = Some(p);
            let mb = k.block(&[], Some(e));
            members.push(k.func_vis("m", &[], mb, Vis::Public));
        }
        items.push(k.class(&format!("C{i}"), &[base], &members, false));
    }
    let hir = k.finish(&items);
    let r = Resolver::new(Policy::php())
        .resolve(hir.clone(), &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, last_path.unwrap()).0, item_res(0, kc));
    // A tight member budget stops it cleanly.
    let tight = resolve_lang::Budget::default().with_member_steps(10);
    let err = Resolver::new(Policy::php())
        .with_budget(tight)
        .resolve(hir, &k.names)
        .unwrap_err();
    assert!(matches!(
        err,
        resolve_lang::ResolveError::BudgetExceeded { .. }
    ));
}

#[test]
fn test_class_inheritance_cycle_terminates() {
    let mut k = Kit::new();
    let (ta, _) = k.ty(&["B"]);
    let (e, p) = k.use_root(&["missing"], PathRoot::SelfType);
    let mb = k.block(&[], Some(e));
    let m = k.func_vis("m", &[], mb, Vis::Public);
    let a = k.class("A", &[ta], &[m], false);
    let (tb, _) = k.ty(&["A"]);
    let b = k.class("B", &[tb], &[], false);
    let hir = k.finish(&[a, b]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert!(r.is_clean());
    // Not statically known: left type-directed.
    assert_eq!(res(&r, 0, p), (Res::Unresolved, 1));
}

#[test]
fn test_item_kind_names_in_policy_classes() {
    assert_eq!(
        resolve_lang::ItemClass::of(&ItemKind::Import {
            path: hir_lang::PathId::from_index(0).unwrap(),
            glob: false
        }),
        Some(resolve_lang::ItemClass::Import)
    );
}
