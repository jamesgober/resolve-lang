//! Classes under `Policy::php()`: a class name in value position (the
//! operand of `new`, the right side of `instanceof`, `Foo::class`, static
//! receivers) and interface members reached through implementing classes
//! (`Impl::CONST`). Worked cases, the shapes bcgen-lang 0.4 compiles, and a
//! differential property against a reference of PHP's lookup order.

#![allow(clippy::unwrap_used, clippy::expect_used)]

mod common;

use common::{Kit, item_res, kinds, messages, res};
use hir_lang::{
    ClassDef, Def, Expr, ExprId, InterfaceDef, Intrinsic, ItemId, ItemKind, List, Name, Ns, Path,
    PathId, PathRoot, Res, TyId, UnitId, Vis,
};
use proptest::prelude::*;
use resolve_lang::{
    Budget, DefKind, DiagKind, Export, ItemClass, Limit, MapEnv, Namespace, NsSet, Policy,
    ResolveError, Resolver, Target,
};

/// `mox.new(class, args..)` as the Mox sketch's `new_object` template writes
/// it: the callee is the extern `mox.new`, already resolved.
fn mox_new(k: &mut Kit, class: ExprId, args: &[ExprId]) -> ExprId {
    let sym = k.names.intern("mox.new");
    let p =
        k.b.resolved_path(Name::new(sym), Ns::Value, Res::Extern(sym));
    let callee = k.b.expr(Expr::Path(p));
    let mut all = vec![class];
    all.extend_from_slice(args);
    k.b.call(callee, &all)
}

/// `mox.instanceof(x, class)`, the intrinsic.
fn mox_instanceof(k: &mut Kit, x: ExprId, class: ExprId) -> ExprId {
    let sym = k.names.intern("mox.instanceof");
    let args = k.b.list(&[x, class]);
    k.b.expr(Expr::Intrinsic {
        kind: Intrinsic::Named(sym),
        generic_args: List::EMPTY,
        args,
    })
}

fn interface(k: &mut Kit, name: &str, supers: &[&str], items: &[ItemId]) -> ItemId {
    let supers: Vec<TyId> = supers.iter().map(|s| k.ty(&[s]).0).collect();
    let supers = k.b.list(&supers);
    let items = k.b.list(items);
    k.item(
        name,
        ItemKind::Interface(InterfaceDef {
            supers,
            items,
            ..InterfaceDef::default()
        }),
        Vis::Public,
    )
}

fn class_impl(
    k: &mut Kit,
    name: &str,
    base: Option<&str>,
    ifaces: &[&str],
    items: &[ItemId],
) -> ItemId {
    let bases: Vec<TyId> = base.iter().map(|b| k.ty(&[b]).0).collect();
    let ifaces: Vec<TyId> = ifaces.iter().map(|i| k.ty(&[i]).0).collect();
    let bases = k.b.list(&bases);
    let interfaces = k.b.list(&ifaces);
    let items = k.b.list(items);
    k.item(
        name,
        ItemKind::Class(ClassDef {
            bases,
            interfaces,
            items,
            ..ClassDef::default()
        }),
        Vis::Public,
    )
}

fn path_of(hir: &hir_lang::Hir, e: ExprId) -> PathId {
    let Expr::Path(p) = *hir.expr(e) else {
        panic!("not a path")
    };
    p
}

// ------------------------------------------------------------- class values

/// What bcgen-lang 0.4's class operations expect of the operand: a path with
/// the class item as its whole resolution (`tests/common/hb.rs::item_ref`).
#[test]
fn test_new_operand_resolves_to_the_shape_bcgen_expects() {
    // class Foo { function __construct($n) {} }   new Foo(1)  ==  mox.new(Foo, 1)
    // The same program is built twice: with the operand left for the
    // resolver, and with it resolved by hand the way bcgen-lang's tests do.
    let build = |hand: bool| {
        let mut k = Kit::new();
        let (p, _) = k.param("n");
        let body = k.block(&[], None);
        let ctor = k.func_vis("__construct", &[p], body, Vis::Public);
        let class_foo = k.class("Foo", &[], &[ctor], false);
        let operand = if hand {
            let d = k.b.def(Def::Item(class_foo));
            let segs = k.segs(&["Foo"]);
            let path = k.b.path(Path {
                res: Res::Def(d),
                ..Path::new(segs, Ns::Value)
            });
            k.b.expr(Expr::Path(path))
        } else {
            k.use_(&["Foo"]).0
        };
        let one = k.b.int(1);
        let call = mox_new(&mut k, operand, &[one]);
        let body = k.block(&[], Some(call));
        let main = k.func("main", &[], body);
        let hir = k.finish(&[class_foo, main]);
        (hir, k, operand)
    };
    let (by_hand, _, hand_operand) = build(true);
    let (unresolved, k, operand) = build(false);
    let r = Resolver::new(Policy::php())
        .with_env(&MapEnv::new())
        .resolve(unresolved, &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    let hir = r.hir(UnitId::new(0)).unwrap();
    let got = *hir.path(path_of(hir, operand));
    let want = *by_hand.path(path_of(&by_hand, hand_operand));
    assert_eq!(got.res, want.res);
    assert_eq!(got.unresolved, want.unresolved);
    assert_eq!(got.root, want.root);
    assert_eq!(got.ns, want.ns);
    assert_eq!(got.qself, want.qself);
    assert_eq!(got.segments.len(), want.segments.len());
    assert!(hir.validate().is_ok());
}

/// Every form of a class name in value position, in one unit.
struct Forms {
    hir: hir_lang::Hir,
    k: Kit,
    class_foo: ItemId,
    shape: ItemId,
    bar: ItemId,
    konst: ItemId,
    new_op: PathId,
    new_folded: PathId,
    inst_class: PathId,
    inst_iface: PathId,
    class_const: PathId,
    iface_class_const: PathId,
    static_call: PathId,
    class_konst: PathId,
}

fn forms() -> Forms {
    // interface Shape {}
    // class Foo { const C = 1; static function bar() {} }
    // function main($x) {
    //     mox.new(Foo, 1); mox.new(foo); mox.instanceof($x, Foo); mox.instanceof($x, Shape);
    //     Foo::class; Foo::bar(); Foo::C;
    // }
    let mut k = Kit::new();
    let shape = interface(&mut k, "Shape", &[], &[]);
    let konst = k.constant("C", Vis::Public);
    let bb = k.block(&[], None);
    let bar = k.func_vis("bar", &[], bb, Vis::Public);
    let class_foo = k.class("Foo", &[], &[konst, bar], false);
    let (px, bx) = k.param("x");
    let (a, new_op) = k.use_(&["Foo"]);
    let one = k.b.int(1);
    let n1 = mox_new(&mut k, a, &[one]);
    let (a, new_folded) = k.use_(&["foo"]);
    let n2 = mox_new(&mut k, a, &[]);
    let x = k.b.use_binder(bx);
    let (a, inst_class) = k.use_(&["Foo"]);
    let i1 = mox_instanceof(&mut k, x, a);
    let x = k.b.use_binder(bx);
    let (a, inst_iface) = k.use_(&["Shape"]);
    let i2 = mox_instanceof(&mut k, x, a);
    let (c1, class_const) = k.use_(&["Foo", "class"]);
    let (c4, iface_class_const) = k.use_(&["Shape", "class"]);
    let (callee, static_call) = k.use_(&["Foo", "bar"]);
    let c2 = k.b.call(callee, &[]);
    let (c3, class_konst) = k.use_(&["Foo", "C"]);
    let t = k.tuple(&[n1, n2, i1, i2, c1, c2, c3, c4]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[px], body);
    let hir = k.finish(&[shape, class_foo, main]);
    Forms {
        hir,
        k,
        class_foo,
        shape,
        bar,
        konst,
        new_op,
        new_folded,
        inst_class,
        inst_iface,
        class_const,
        iface_class_const,
        static_call,
        class_konst,
    }
}

#[test]
fn test_class_names_resolve_in_every_value_position_under_php() {
    let f = forms();
    let r = Resolver::new(Policy::php())
        .resolve(f.hir, &f.k.names)
        .unwrap();
    // The one diagnostic is the interface operand (below).
    assert_eq!(kinds(&r).len(), 1, "{:?}", messages(&r, &f.k.names));
    let class_foo = (item_res(0, f.class_foo), 0);
    // The operand of `new`, folded by PHP's case rules, and `instanceof`.
    assert_eq!(res(&r, 0, f.new_op), class_foo);
    assert_eq!(res(&r, 0, f.new_folded), class_foo);
    assert_eq!(res(&r, 0, f.inst_class), class_foo);
    // `Foo::class` is the class with the member name left over, the shape
    // bcgen-lang's `class_name_path` reads; so is an interface's.
    assert_eq!(res(&r, 0, f.class_const), (item_res(0, f.class_foo), 1));
    assert_eq!(res(&r, 0, f.iface_class_const), (item_res(0, f.shape), 1));
    // Static call and constant receivers.
    assert_eq!(res(&r, 0, f.static_call), (item_res(0, f.bar), 0));
    assert_eq!(res(&r, 0, f.class_konst), (item_res(0, f.konst), 0));
    // HIR cannot name an interface in a value path (hir-lang refuses the
    // resolution), so it stays what it was: `instanceof` takes it as a type
    // argument instead.
    assert_eq!(res(&r, 0, f.inst_iface).0, Res::Err);
    assert!(matches!(
        kinds(&r)[0],
        DiagKind::WrongKind {
            found: DefKind::Interface,
            ..
        }
    ));
    assert!(
        r.hir(UnitId::new(0)).unwrap().validate().is_ok(),
        "hir-lang accepts the resolutions"
    );
}

#[test]
fn test_class_value_references_are_indexed() {
    let f = forms();
    let r = Resolver::new(Policy::php())
        .resolve(f.hir, &f.k.names)
        .unwrap();
    let ix = r.index();
    let Res::Def(d) = item_res(0, f.class_foo) else {
        unreachable!()
    };
    let def = ix.def_of(Target::Def(d)).unwrap();
    // new Foo, new foo, instanceof Foo, Foo::class, Foo::bar, Foo::C.
    assert_eq!(ix.references(def).len(), 6);
}

#[test]
fn test_class_value_fallback_is_opt_in_and_documented() {
    // Without the rule a class in value position is the diagnostic it was.
    let f = forms();
    let policy = Policy::php().with_class_values(false);
    assert!(!policy.class_values());
    let r = Resolver::new(policy).resolve(f.hir, &f.k.names).unwrap();
    let wrong = kinds(&r)
        .into_iter()
        .filter(|d| matches!(d, DiagKind::WrongKind { .. }))
        .count();
    // `new Foo`, `new foo`, `instanceof Foo`, `instanceof Shape`.
    assert_eq!(wrong, 4, "{:?}", messages(&r, &f.k.names));
    assert_eq!(
        messages(&r, &f.k.names)[0],
        "expected a value, found class `Foo`"
    );
    assert_eq!(res(&r, 0, f.new_op).0, Res::Err);
    // Other presets are unchanged: they do not turn it on.
    assert!(!Policy::kraken().class_values());
    assert!(!Policy::python().class_values());
    assert!(Policy::php().class_values());
}

#[test]
fn test_calling_a_class_name_is_still_wrong_and_constants_win() {
    // class Foo {}   const Foo = 1;   class Bar {}
    // main() { (Foo, Foo(), Bar()) }
    let mut k = Kit::new();
    let class_foo = k.class("Foo", &[], &[], false);
    let konst = k.constant("Foo", Vis::Public);
    let bar = k.class("Bar", &[], &[], false);
    let (a, as_value) = k.use_(&["Foo"]);
    let (callee, _) = k.use_(&["Foo"]);
    let call_foo = k.b.call(callee, &[]);
    let (callee, call_path) = k.use_(&["Bar"]);
    let call_bar = k.b.call(callee, &[]);
    let t = k.tuple(&[a, call_foo, call_bar]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[class_foo, konst, bar, main]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    // The constant beats the class for a plain value; `Foo()` finds the
    // constant (PHP's lenient callee lookup); `Bar()` finds no function and
    // is not `new Bar`.
    assert_eq!(res(&r, 0, as_value).0, item_res(0, konst));
    assert_eq!(res(&r, 0, call_path).0, Res::Err);
    let ks = kinds(&r);
    assert_eq!(ks.len(), 1, "{:?}", messages(&r, &k.names));
    assert!(matches!(ks[0], DiagKind::WrongKind { .. }));
}

#[test]
fn test_callee_rule_holds_without_php_split_tables() {
    // A policy that keeps classes out of the value table but has no separate
    // constant table: `Foo` as a value finds the class, `Foo()` does not.
    let policy = Policy::new()
        .with_occupies(ItemClass::Class, NsSet::single(Namespace::Type))
        .with_class_values(true);
    let mut k = Kit::new();
    let class_foo = k.class("Foo", &[], &[], false);
    let (a, as_value) = k.use_(&["Foo"]);
    let (callee, as_callee) = k.use_(&["Foo"]);
    let call = k.b.call(callee, &[]);
    let t = k.tuple(&[a, call]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[class_foo, main]);
    let r = Resolver::new(policy).resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, as_value), (item_res(0, class_foo), 0));
    assert_eq!(res(&r, 0, as_callee).0, Res::Err);
    assert!(matches!(kinds(&r)[..], [DiagKind::WrongKind { .. }]));
}

#[test]
fn test_unknown_class_in_value_position_is_unresolved_with_a_suggestion() {
    // class Counter {}   main() { mox.new(Countr) }
    let mut k = Kit::new();
    let counter = k.class("Counter", &[], &[], false);
    let (a, p) = k.use_(&["Countr"]);
    let n = mox_new(&mut k, a, &[]);
    let body = k.block(&[], Some(n));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[counter, main]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p).0, Res::Err);
    let ds = r.diagnostics();
    assert_eq!(ds.len(), 1);
    assert!(matches!(ds[0].kind, DiagKind::Unresolved { .. }));
    assert!(
        ds[0].message(&k.names).contains("Counter"),
        "{}",
        ds[0].message(&k.names)
    );
}

#[test]
fn test_namespaced_and_imported_class_names_resolve_as_values() {
    // namespace App { class Foo {} }   use App\Foo as Bar;
    // main() { (App\Foo, \App\Foo, Bar) }
    let mut k = Kit::new();
    let class_foo = k.class("Foo", &[], &[], false);
    let app = k.module("App", &[class_foo], Vis::Public);
    let (imp, _) = k.import(&["App", "Foo"], Some("Bar"), Vis::Private);
    let (a, rel) = k.use_(&["App", "Foo"]);
    let (b, abs) = k.use_root(&["App", "Foo"], PathRoot::Global);
    let (c, aliased) = k.use_(&["Bar"]);
    let t = k.tuple(&[a, b, c]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[app, imp, main]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    for p in [rel, abs, aliased] {
        assert_eq!(res(&r, 0, p), (item_res(0, class_foo), 0), "{p:?}");
    }
}

#[test]
fn test_host_defined_classes_resolve_as_values() {
    // Exception is the host's (prelude); Ext\Cls is a host class in a host
    // module.
    let mut k = Kit::new();
    let exception = k.names.intern("Exception");
    let ext = k.names.intern("Ext");
    let cls = k.names.intern("Cls");
    let ext_res = Res::Extern(ext);
    let cls_res = Res::Extern(cls);
    let env = MapEnv::new()
        .with_prelude(
            Name::new(exception),
            Namespace::Type,
            Export::new(Res::Extern(exception), DefKind::Class { mixin: false }),
        )
        .with_root(Name::new(ext), Export::new(ext_res, DefKind::Module))
        .with_member(
            ext_res,
            Name::new(cls),
            Namespace::Type,
            Export::new(cls_res, DefKind::Class { mixin: false }),
        );
    let (a, p_exception) = k.use_(&["Exception"]);
    let (b, p_ext) = k.use_(&["Ext", "Cls"]);
    let t = k.tuple(&[a, b]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[main]);
    let r = Resolver::new(Policy::php())
        .with_env(&env)
        .resolve(hir, &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p_exception), (Res::Extern(exception), 0));
    assert_eq!(res(&r, 0, p_ext), (cls_res, 0));
}

// ------------------------------------------------------- interface members

/// interface I { const X = 1; function m(); }
/// interface J extends I { }
/// class Impl implements I { function reads() { self::X } }
/// class Child extends Impl { }
/// class ViaJ implements J { }
/// class Own implements I { const X = 2; }
/// abstract class Abs implements I { }
/// main() { (Impl::X, Child::X, ViaJ::X, Own::X, Abs::m, Impl::Y) }
struct Ifaces {
    hir: hir_lang::Hir,
    k: Kit,
    imp: ItemId,
    i_x: ItemId,
    i_m: ItemId,
    own_x: ItemId,
    impl_x: PathId,
    child_x: PathId,
    via_j_x: PathId,
    own_x_use: PathId,
    abs_m: PathId,
    impl_y: PathId,
    self_x: PathId,
}

fn ifaces() -> Ifaces {
    let mut k = Kit::new();
    let i_x = k.constant("X", Vis::Public);
    let mb = k.block(&[], None);
    let i_m = k.func_vis("m", &[], mb, Vis::Public);
    let i = interface(&mut k, "I", &[], &[i_x, i_m]);
    let j = interface(&mut k, "J", &["I"], &[]);
    let (e, self_x) = k.use_root(&["X"], PathRoot::SelfType);
    let sb = k.block(&[], Some(e));
    let reads_x = k.func_vis("reads", &[], sb, Vis::Public);
    let imp = class_impl(&mut k, "Impl", None, &["I"], &[reads_x]);
    let child = class_impl(&mut k, "Child", Some("Impl"), &[], &[]);
    let via_j = class_impl(&mut k, "ViaJ", None, &["J"], &[]);
    let own_x = k.constant("X", Vis::Public);
    let own = class_impl(&mut k, "Own", None, &["I"], &[own_x]);
    let abs = class_impl(&mut k, "Abs", None, &["I"], &[]);
    let (a, impl_x) = k.use_(&["Impl", "X"]);
    let (b, child_x) = k.use_(&["Child", "X"]);
    let (c, via_j_x) = k.use_(&["ViaJ", "X"]);
    let (d, own_x_use) = k.use_(&["Own", "X"]);
    let (e, abs_m) = k.use_(&["Abs", "m"]);
    let (f, impl_y) = k.use_(&["Impl", "Y"]);
    let t = k.tuple(&[a, b, c, d, e, f]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[i, j, imp, child, via_j, own, abs, main]);
    Ifaces {
        hir,
        k,
        imp,
        i_x,
        i_m,
        own_x,
        impl_x,
        child_x,
        via_j_x,
        own_x_use,
        abs_m,
        impl_y,
        self_x,
    }
}

#[test]
fn test_interface_constants_resolve_through_implementing_classes() {
    let f = ifaces();
    let r = Resolver::new(Policy::php())
        .resolve(f.hir, &f.k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &f.k.names));
    let x = (item_res(0, f.i_x), 0);
    // Directly implemented, through a base class, through a super-interface.
    assert_eq!(res(&r, 0, f.impl_x), x);
    assert_eq!(res(&r, 0, f.child_x), x);
    assert_eq!(res(&r, 0, f.via_j_x), x);
    // `self::X` inside the implementing class.
    assert_eq!(res(&r, 0, f.self_x), x);
    // The class's own constant overrides the interface's (PHP 8.1).
    assert_eq!(res(&r, 0, f.own_x_use), (item_res(0, f.own_x), 0));
    // An abstract class reaches the interface's method.
    assert_eq!(res(&r, 0, f.abs_m), (item_res(0, f.i_m), 0));
    // A name nobody declares is left to the type checker, as before.
    assert_eq!(res(&r, 0, f.impl_y), (item_res(0, f.imp), 1));
    assert!(r.hir(UnitId::new(0)).unwrap().validate().is_ok());
}

#[test]
fn test_interface_members_are_off_for_other_policies() {
    for policy in [
        Policy::php().with_interface_members(false),
        Policy::python(),
    ] {
        let f = ifaces();
        let r = Resolver::new(policy).resolve(f.hir, &f.k.names).unwrap();
        // Left on the class with the member name unresolved, as in 0.4.0.
        assert_eq!(res(&r, 0, f.impl_x).1, 1);
        assert_eq!(res(&r, 0, f.child_x).1, 1);
        assert_eq!(res(&r, 0, f.abs_m).1, 1);
        // Declared on the class itself: still resolved.
        assert_eq!(res(&r, 0, f.own_x_use), (item_res(0, f.own_x), 0));
    }
    assert!(!Policy::kraken().interface_members());
    assert!(Policy::php().interface_members());
}

#[test]
fn test_interface_constant_reference_is_indexed_and_renamed() {
    let f = ifaces();
    let r = Resolver::new(Policy::php())
        .resolve(f.hir, &f.k.names)
        .unwrap();
    let ix = r.index();
    let Res::Def(d) = item_res(0, f.i_x) else {
        unreachable!()
    };
    let def = ix.def_of(Target::Def(d)).unwrap();
    // Impl::X, Child::X, ViaJ::X and self::X.
    assert_eq!(ix.references(def).len(), 4);
    assert_eq!(ix.rename_set(def).edits.len(), 5);
}

#[test]
fn test_interface_hierarchies_that_loop_terminate() {
    // interface I extends I { const X; }   class A implements A {}   class B implements I, B {}
    // main() { (A::X, B::X) }
    let mut k = Kit::new();
    let x = k.constant("X", Vis::Public);
    let i = interface(&mut k, "I", &["I"], &[x]);
    let a = class_impl(&mut k, "A", None, &["A"], &[]);
    let b = class_impl(&mut k, "B", None, &["I", "B"], &[]);
    let (e1, pa) = k.use_(&["A", "X"]);
    let (e2, pb) = k.use_(&["B", "X"]);
    let t = k.tuple(&[e1, e2]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[i, a, b, main]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, pa), (item_res(0, a), 1));
    assert_eq!(res(&r, 0, pb), (item_res(0, x), 0));
}

#[test]
fn test_deep_class_chain_with_the_interface_at_the_top_is_linear() {
    // interface I { const X; }   class C0 implements I {}   class Ck extends C(k-1)
    // main() { (C0::X, C97::X, ..) }: every lookup walks the chain at most once.
    let n = 20_000usize;
    let mut k = Kit::new();
    let x = k.constant("X", Vis::Public);
    let i = interface(&mut k, "I", &[], &[x]);
    let mut items = vec![i];
    let mut paths = Vec::new();
    let mut uses = Vec::new();
    for c in 0..n {
        let base = (c > 0).then(|| format!("C{}", c - 1));
        let ifaces: &[&str] = if c == 0 { &["I"] } else { &[] };
        let name = format!("C{c}");
        items.push(class_impl(&mut k, &name, base.as_deref(), ifaces, &[]));
    }
    for c in (0..n).step_by(97) {
        let (e, p) = k.use_(&[&format!("C{c}"), "X"]);
        uses.push(e);
        paths.push(p);
    }
    let t = k.tuple(&uses);
    let body = k.block(&[], Some(t));
    items.push(k.func("main", &[], body));
    let hir = k.finish(&items);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names).first());
    for p in paths {
        assert_eq!(res(&r, 0, p), (item_res(0, x), 0));
    }
}

// ------------------------------------------------- differential property

/// One node of a random PHP hierarchy: a class or an interface.
#[derive(Clone, Debug)]
struct Node {
    interface: bool,
    /// A class's parent, or an interface's super-interfaces (earlier nodes).
    bases: Vec<usize>,
    /// A class's implemented interfaces (earlier nodes that are interfaces).
    implements: Vec<usize>,
    /// Whether it declares each constant K0..K2.
    declares: [bool; 3],
}

type RawNode = (bool, Vec<usize>, Vec<usize>, [bool; 3]);

fn hierarchy() -> impl Strategy<Value = Vec<Node>> {
    (2usize..9)
        .prop_flat_map(|n| {
            let node = |i: usize| {
                (
                    any::<bool>(),
                    proptest::collection::vec(0..i.max(1), 0..3),
                    proptest::collection::vec(0..i.max(1), 0..3),
                    proptest::array::uniform3(proptest::bool::weighted(0.3)),
                )
            };
            (0..n).map(node).collect::<Vec<_>>()
        })
        .prop_map(|raw: Vec<RawNode>| {
            let mut nodes: Vec<Node> = Vec::new();
            for (i, (interface, bases, implements, declares)) in raw.into_iter().enumerate() {
                let is_iface = |j: usize, nodes: &[Node]| nodes.get(j).is_some_and(|n| n.interface);
                let interface = interface || i == 0;
                let mut bs: Vec<usize> = Vec::new();
                let mut ims: Vec<usize> = Vec::new();
                if interface {
                    for b in bases {
                        if b < i && is_iface(b, &nodes) && !bs.contains(&b) {
                            bs.push(b);
                        }
                    }
                } else {
                    // At most one parent class, and distinct interfaces.
                    if let Some(&b) = bases.first() {
                        if b < i && !is_iface(b, &nodes) {
                            bs.push(b);
                        }
                    }
                    for m in implements {
                        if m < i && is_iface(m, &nodes) && !ims.contains(&m) {
                            ims.push(m);
                        }
                    }
                }
                nodes.push(Node {
                    interface,
                    bases: bs,
                    implements: ims,
                    declares,
                });
            }
            nodes
        })
}

/// The C3 order of an interface (itself first) over its super-interfaces,
/// by the textbook merge; an inconsistent one falls back to its bases'
/// orders concatenated without repeats, as the resolver does.
fn iface_order(nodes: &[Node], i: usize, memo: &mut Vec<Option<Vec<usize>>>) -> Vec<usize> {
    if let Some(o) = &memo[i] {
        return o.clone();
    }
    let bases = &nodes[i].bases;
    let order = if bases.len() < 2 {
        let mut out = vec![i];
        if let Some(&b) = bases.first() {
            out.extend(iface_order(nodes, b, memo));
        }
        out
    } else {
        let mut lists: Vec<Vec<usize>> =
            bases.iter().map(|&b| iface_order(nodes, b, memo)).collect();
        lists.push(bases.clone());
        let mut out = vec![i];
        let ok = loop {
            lists.retain(|l| !l.is_empty());
            if lists.is_empty() {
                break true;
            }
            let pick = lists
                .iter()
                .map(|l| l[0])
                .find(|h| !lists.iter().any(|l| l[1..].contains(h)));
            let Some(h) = pick else { break false };
            out.push(h);
            for l in &mut lists {
                if l[0] == h {
                    l.remove(0);
                }
            }
        };
        if !ok {
            out = vec![i];
            for &b in bases {
                for x in iface_order(nodes, b, memo) {
                    if !out.contains(&x) {
                        out.push(x);
                    }
                }
            }
        }
        out
    };
    memo[i] = Some(order.clone());
    order
}

/// PHP's lookup order for constant `n` on node `c`: the class and its
/// ancestors' own declarations first, then the interfaces, nearest class
/// first, each with its super-interfaces. (Two declarations PHP would call
/// ambiguous are ordered the same way here as by the resolver; the property
/// is about everything else: that a declaration is found at all, and that
/// the nearer of an override and an inherited one wins.)
fn expected(
    nodes: &[Node],
    c: usize,
    n: usize,
    memo: &mut Vec<Option<Vec<usize>>>,
) -> Option<usize> {
    if nodes[c].interface {
        return iface_order(nodes, c, memo)
            .into_iter()
            .find(|&k| nodes[k].declares[n]);
    }
    let mut chain = vec![c];
    let mut cur = c;
    while let Some(&p) = nodes[cur].bases.first() {
        chain.push(p);
        cur = p;
    }
    if let Some(&k) = chain.iter().find(|&&k| nodes[k].declares[n]) {
        return Some(k);
    }
    for &k in &chain {
        for &i in &nodes[k].implements {
            if let Some(d) = iface_order(nodes, i, memo)
                .into_iter()
                .find(|&d| nodes[d].declares[n])
            {
                return Some(d);
            }
        }
    }
    None
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// `Ni::Kn` follows PHP's lookup (own, ancestors, then interfaces), for
    /// random class and interface hierarchies, and is left type-directed
    /// when nothing declares it.
    #[test]
    fn prop_interface_constants_follow_php_lookup(nodes in hierarchy()) {
        let mut k = Kit::new();
        let mut items = Vec::new();
        let mut consts: Vec<[Option<ItemId>; 3]> = Vec::new();
        let mut node_items = Vec::new();
        for (i, n) in nodes.iter().enumerate() {
            let mut own = Vec::new();
            let mut cs = [None; 3];
            for (c, declared) in n.declares.iter().enumerate() {
                if *declared {
                    let it = k.constant(&format!("K{c}"), Vis::Public);
                    cs[c] = Some(it);
                    own.push(it);
                }
            }
            let name = format!("N{i}");
            let it = if n.interface {
                let supers: Vec<String> = n.bases.iter().map(|b| format!("N{b}")).collect();
                let refs: Vec<&str> = supers.iter().map(String::as_str).collect();
                interface(&mut k, &name, &refs, &own)
            } else {
                let base = n.bases.first().map(|b| format!("N{b}"));
                let ims: Vec<String> = n.implements.iter().map(|b| format!("N{b}")).collect();
                let refs: Vec<&str> = ims.iter().map(String::as_str).collect();
                class_impl(&mut k, &name, base.as_deref(), &refs, &own)
            };
            consts.push(cs);
            node_items.push(it);
            items.push(it);
        }
        let mut uses = Vec::new();
        let mut paths = Vec::new();
        for i in 0..nodes.len() {
            for c in 0..3 {
                let (e, p) = k.use_(&[&format!("N{i}"), &format!("K{c}")]);
                uses.push(e);
                paths.push((i, c, p));
            }
        }
        let t = k.tuple(&uses);
        let body = k.block(&[], Some(t));
        items.push(k.func("main", &[], body));
        let hir = k.finish(&items);
        let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
        let mut memo = vec![None; nodes.len()];
        for (i, c, p) in paths {
            let want = match expected(&nodes, i, c, &mut memo) {
                Some(owner) => (item_res(0, consts[owner][c].unwrap()), 0),
                None => (item_res(0, node_items[i]), 1),
            };
            prop_assert_eq!(res(&r, 0, p), want, "N{}::K{} in {:?}", i, c, nodes);
        }
        prop_assert!(r.hir(UnitId::new(0)).unwrap().validate().is_ok());
    }
}

#[test]
fn test_class_implementing_many_interfaces_stays_within_the_member_budget() {
    // class W implements J0..J(n-1), each Ji declaring constant Ci.
    // `W::Ci` resolves for every i; `W::Zk` (nobody declares it) walks every
    // interface, so enough of them exhaust a small budget with an error, not
    // a hang.
    let n = 600usize;
    let build = |misses: usize| {
        let mut k = Kit::new();
        let mut items = Vec::new();
        let mut consts = Vec::new();
        for i in 0..n {
            let c = k.constant(&format!("C{i}"), Vis::Public);
            consts.push(c);
            items.push(interface(&mut k, &format!("J{i}"), &[], &[c]));
        }
        let names: Vec<String> = (0..n).map(|i| format!("J{i}")).collect();
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        items.push(class_impl(&mut k, "W", None, &refs, &[]));
        let mut uses = Vec::new();
        let mut hits = Vec::new();
        for i in 0..n {
            let (e, p) = k.use_(&["W", &format!("C{i}")]);
            uses.push(e);
            hits.push(p);
        }
        for z in 0..misses {
            uses.push(k.use_(&["W", &format!("Z{z}")]).0);
        }
        let t = k.tuple(&uses);
        let body = k.block(&[], Some(t));
        items.push(k.func("main", &[], body));
        (k.finish(&items), k, consts, hits)
    };
    // Within the default budget: every constant found.
    let (hir, k, consts, hits) = build(50);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    for (c, p) in consts.iter().zip(&hits) {
        assert_eq!(res(&r, 0, *p), (item_res(0, *c), 0));
    }
    // Over a small one: a budget error.
    let (hir, k, _, _) = build(600);
    let tight = Budget::default().with_member_steps(50_000);
    let err = Resolver::new(Policy::php())
        .with_budget(tight)
        .resolve(hir, &k.names)
        .unwrap_err();
    assert!(matches!(
        err,
        ResolveError::BudgetExceeded {
            limit: Limit::MemberSteps
        }
    ));
}

#[test]
fn test_deep_interface_chain_and_deep_class_chain_do_not_overflow() {
    // interface I0 { const X; }  interface Ik extends I(k-1)  class C implements I(n-1)
    let n = 50_000usize;
    let mut k = Kit::new();
    let x = k.constant("X", Vis::Public);
    let mut items = vec![interface(&mut k, "I0", &[], &[x])];
    for i in 1..n {
        items.push(interface(
            &mut k,
            &format!("I{i}"),
            &[&format!("I{}", i - 1)],
            &[],
        ));
    }
    items.push(class_impl(
        &mut k,
        "C",
        None,
        &[&format!("I{}", n - 1)],
        &[],
    ));
    let (e, p) = k.use_(&["C", "X"]);
    let t = k.tuple(&[e]);
    let body = k.block(&[], Some(t));
    items.push(k.func("main", &[], body));
    let hir = k.finish(&items);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names).first());
    assert_eq!(res(&r, 0, p), (item_res(0, x), 0));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// A class named in value position resolves to its item whatever the
    /// ASCII case of the spelling (PHP folds class names); a name no class
    /// has is one `Unresolved` diagnostic and never a class.
    #[test]
    fn prop_class_values_fold_case_and_unknown_names_are_errors(
        picks in proptest::collection::vec((0usize..6, any::<u8>()), 1..24),
    ) {
        let mut k = Kit::new();
        let names = ["Alpha", "Beta", "Gamma", "delta", "Epsilon", "Zeta"];
        let declared = 4usize;
        let mut items = Vec::new();
        for n in &names[..declared] {
            items.push(k.class(n, &[], &[], false));
        }
        let mut uses = Vec::new();
        let mut wants = Vec::new();
        for (which, flips) in &picks {
            // Flip the case of letters selected by the bits of `flips`.
            let spelled: String = names[*which]
                .chars()
                .enumerate()
                .map(|(i, c)| {
                    if (flips >> (i % 8)) & 1 == 1 {
                        if c.is_ascii_lowercase() { c.to_ascii_uppercase() } else { c.to_ascii_lowercase() }
                    } else {
                        c
                    }
                })
                .collect();
            let (e, p) = k.use_(&[&spelled]);
            uses.push(e);
            wants.push((p, *which));
        }
        let t = k.tuple(&uses);
        let body = k.block(&[], Some(t));
        items.push(k.func("main", &[], body));
        let hir = k.finish(&items);
        let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
        let mut errors = 0;
        for (p, which) in wants {
            if which < declared {
                prop_assert_eq!(res(&r, 0, p), (item_res(0, items[which]), 0));
            } else {
                errors += 1;
                prop_assert_eq!(res(&r, 0, p).0, Res::Err);
            }
        }
        let unresolved = kinds(&r)
            .iter()
            .filter(|d| matches!(d, DiagKind::Unresolved { .. }))
            .count();
        prop_assert_eq!(unresolved, errors);
        prop_assert!(r.hir(UnitId::new(0)).unwrap().validate().is_ok());
    }
}

#[test]
fn test_generator_makes_classes_with_interfaces_and_overrides() {
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;
    let mut runner = TestRunner::deterministic();
    let (mut through_iface, mut through_class, mut missing) = (0, 0, 0);
    for _ in 0..300 {
        let nodes = hierarchy().new_tree(&mut runner).unwrap().current();
        let mut memo = vec![None; nodes.len()];
        for c in 0..nodes.len() {
            for n in 0..3 {
                match expected(&nodes, c, n, &mut memo) {
                    Some(o) if o == c => {}
                    Some(o) if nodes[o].interface && !nodes[c].interface => through_iface += 1,
                    Some(_) => through_class += 1,
                    None => missing += 1,
                }
            }
        }
    }
    assert!(through_iface > 100 && through_class > 50 && missing > 100);
}
