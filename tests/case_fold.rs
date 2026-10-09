//! PHP name tables: ASCII case folding for functions, methods, and classes;
//! case-sensitive constants in a table of their own; the call position
//! choosing which table is searched first. Checked against a reference made
//! of plain maps on random programs, plus worked examples.

#![allow(clippy::unwrap_used, clippy::expect_used)]

mod common;

use std::collections::BTreeMap;

use common::{Kit, item_res, kinds, messages, res};
use hir_lang::{
    BinderKind, Ident, ItemId, MixinAction, MixinRule, Ns, PathId, PathRoot, Res, Span, Stmt, Vis,
};
use proptest::prelude::*;
use resolve_lang::{Case, DiagKind, Namespace, Policy, Resolver};

// ------------------------------------------------------------ worked cases

#[test]
fn test_php_functions_and_classes_fold_ascii_case() {
    // function strLen() {}  class Foo { const K = 1; }  namespace App { function run() {} }
    // function main() { STRLEN(); strlen(); FOO::K; foo::K; APP::RUN(); }
    let mut k = Kit::new();
    let b = k.block(&[], None);
    let strlen = k.func_vis("strLen", &[], b, Vis::Public);
    let kc = k.constant("K", Vis::Public);
    let foo = k.class("Foo", &[], &[kc], false);
    let rb = k.block(&[], None);
    let run = k.func_vis("run", &[], rb, Vis::Public);
    let app = k.module("App", &[run], Vis::Public);
    let (c1, p1) = k.use_(&["STRLEN"]);
    let call1 = k.b.call(c1, &[]);
    let (c2, p2) = k.use_(&["strlen"]);
    let call2 = k.b.call(c2, &[]);
    let (e3, p3) = k.use_(&["FOO", "K"]);
    let (e4, p4) = k.use_(&["foo", "K"]);
    let (c5, p5) = k.use_(&["APP", "RUN"]);
    let call5 = k.b.call(c5, &[]);
    let t = k.tuple(&[call1, call2, e3, e4, call5]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[strlen, foo, app, main]);
    let r = Resolver::new(Policy::php())
        .resolve(hir.clone(), &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p1), (item_res(0, strlen), 0));
    assert_eq!(res(&r, 0, p2), (item_res(0, strlen), 0));
    assert_eq!(res(&r, 0, p3), (item_res(0, kc), 0));
    assert_eq!(res(&r, 0, p4), (item_res(0, kc), 0));
    assert_eq!(res(&r, 0, p5), (item_res(0, run), 0));
    // The same program under a case-sensitive policy: every case variant
    // fails.
    let r = Resolver::new(Policy::kraken())
        .resolve(hir, &k.names)
        .unwrap();
    assert_eq!(res(&r, 0, p1).0, Res::Err);
    assert_eq!(res(&r, 0, p3).0, Res::Err);
}

#[test]
fn test_php_constants_are_case_sensitive_and_separate_from_functions() {
    // const LIMIT = 1;  function config() {}  const config = 2;
    // function main() { LIMIT; limit; config(); config; CONFIG(); CONFIG; }
    let mut k = Kit::new();
    let limit = k.constant("LIMIT", Vis::Private);
    let b = k.block(&[], None);
    let config_fn = k.func("config", &[], b);
    let config_const = k.constant("config", Vis::Private);
    let (e1, p1) = k.use_(&["LIMIT"]);
    let (e2, p2) = k.use_(&["limit"]);
    let (c3, p3) = k.use_(&["config"]);
    let call3 = k.b.call(c3, &[]);
    let (e4, p4) = k.use_(&["config"]);
    let (c5, p5) = k.use_(&["CONFIG"]);
    let call5 = k.b.call(c5, &[]);
    let (e6, p6) = k.use_(&["CONFIG"]);
    let t = k.tuple(&[e1, e2, call3, e4, call5, e6]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[limit, config_fn, config_const, main]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    // No duplicate: a function and a constant may share a name.
    assert!(
        !kinds(&r)
            .iter()
            .any(|d| matches!(d, DiagKind::Duplicate { .. }))
    );
    assert_eq!(res(&r, 0, p1), (item_res(0, limit), 0));
    assert_eq!(res(&r, 0, p2).0, Res::Err, "constants keep case");
    assert_eq!(
        res(&r, 0, p3),
        (item_res(0, config_fn), 0),
        "a callee prefers the function"
    );
    assert_eq!(
        res(&r, 0, p4),
        (item_res(0, config_const), 0),
        "a value prefers the constant"
    );
    assert_eq!(
        res(&r, 0, p5),
        (item_res(0, config_fn), 0),
        "functions fold"
    );
    // `CONFIG` as a value: no constant spelled so; the function (folded) is
    // the fallback.
    assert_eq!(res(&r, 0, p6), (item_res(0, config_fn), 0));
    let ks = kinds(&r);
    assert_eq!(ks.len(), 1, "{:?}", messages(&r, &k.names));
    assert!(matches!(ks[0], DiagKind::Unresolved { .. }));
}

#[test]
fn test_php_duplicates_differing_only_in_case_are_reported() {
    // function foo() {}  function FOO() {}  class Bar {}  class BAR {}  const X = 1;  const x = 2;
    let mut k = Kit::new();
    let b1 = k.block(&[], None);
    let f1 = k.func("foo", &[], b1);
    let b2 = k.block(&[], None);
    let f2 = k.func("FOO", &[], b2);
    let c1 = k.class("Bar", &[], &[], false);
    let c2 = k.class("BAR", &[], &[], false);
    let x1 = k.constant("X", Vis::Private);
    let x2 = k.constant("x", Vis::Private);
    let hir = k.finish(&[f1, f2, c1, c2, x1, x2]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    let dups = kinds(&r)
        .iter()
        .filter(|d| matches!(d, DiagKind::Duplicate { .. }))
        .count();
    assert_eq!(dups, 2, "{:?}", messages(&r, &k.names));
    // The message names the later definition as written.
    let m = messages(&r, &k.names);
    assert!(m.iter().any(|m| m.contains("`FOO`")), "{m:?}");
    assert!(m.iter().any(|m| m.contains("`BAR`")), "{m:?}");
}

#[test]
fn test_php_method_and_class_constant_share_a_name() {
    // class C { const size = 1; function size() {}
    //   function m() { self::size(); self::size; self::SIZE(); self::SIZE; } }
    // function main() { c::Size(); C::size; }
    let mut k = Kit::new();
    let size_c = k.constant("size", Vis::Public);
    let sb = k.block(&[], None);
    let size_f = k.func_vis("size", &[], sb, Vis::Public);
    let (c1, p1) = k.use_root(&["size"], PathRoot::SelfType);
    let call1 = k.b.call(c1, &[]);
    let (e2, p2) = k.use_root(&["size"], PathRoot::SelfType);
    let (c3, p3) = k.use_root(&["SIZE"], PathRoot::SelfType);
    let call3 = k.b.call(c3, &[]);
    let (e4, p4) = k.use_root(&["SIZE"], PathRoot::SelfType);
    let t = k.tuple(&[call1, e2, call3, e4]);
    let mb = k.block(&[], Some(t));
    let m = k.func_vis("m", &[], mb, Vis::Public);
    let class = k.class("C", &[], &[size_c, size_f, m], false);
    let (c5, p5) = k.use_(&["c", "Size"]);
    let call5 = k.b.call(c5, &[]);
    let (e6, p6) = k.use_(&["C", "size"]);
    let t2 = k.tuple(&[call5, e6]);
    let body = k.block(&[], Some(t2));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[class, main]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p1), (item_res(0, size_f), 0));
    assert_eq!(res(&r, 0, p2), (item_res(0, size_c), 0));
    assert_eq!(res(&r, 0, p3), (item_res(0, size_f), 0), "methods fold");
    // `self::SIZE` as a value: no constant spelled so; the method (folded)
    // is the fallback.
    assert_eq!(res(&r, 0, p4), (item_res(0, size_f), 0));
    assert_eq!(res(&r, 0, p5), (item_res(0, size_f), 0));
    assert_eq!(res(&r, 0, p6), (item_res(0, size_c), 0));
    // Both members are listed, each in its own table, spelled as written.
    let members = r.units()[0].members(class).unwrap();
    let names: Vec<(Namespace, Ident)> = members
        .iter()
        .filter(|m| m.name == k.name("size"))
        .map(|m| (m.namespace, Ident::new(m.name.sym, Span::empty(0))))
        .collect();
    assert_eq!(names.len(), 2);
    assert!(names.iter().any(|(ns, _)| *ns == Namespace::Const));
    assert!(names.iter().any(|(ns, _)| *ns == Namespace::Value));
}

#[test]
fn test_php_mixin_rules_match_method_names_in_any_case() {
    // trait T { function Hello() {} }  class C { use T { HELLO as greet; } function m() { self::greet(); self::GREET(); } }
    let mut k = Kit::new();
    let hb = k.block(&[], None);
    let hello = k.func_vis("Hello", &[], hb, Vis::Public);
    let t = k.class("T", &[], &[hello], true);
    let (ty_t, _) = k.ty(&["T"]);
    let alias = k.ident("greet");
    let rule = MixinRule {
        method: Ident::new(k.name("HELLO").sym, Span::empty(0)),
        from: None,
        action: MixinAction::Alias {
            name: Some(alias),
            vis: None,
        },
    };
    let use_t = k.mixin_use(&[ty_t], &[rule]);
    let (c1, p1) = k.use_root(&["greet"], PathRoot::SelfType);
    let call1 = k.b.call(c1, &[]);
    let (c2, p2) = k.use_root(&["GREET"], PathRoot::SelfType);
    let call2 = k.b.call(c2, &[]);
    let tup = k.tuple(&[call1, call2]);
    let mb = k.block(&[], Some(tup));
    let m = k.func_vis("m", &[], mb, Vis::Public);
    let c = k.class("C", &[], &[use_t, m], false);
    let hir = k.finish(&[t, c]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, p1), (item_res(0, hello), 0));
    assert_eq!(res(&r, 0, p2), (item_res(0, hello), 0));
    let members = r.units()[0].members(c).unwrap();
    assert!(members.iter().any(|m| m.name == k.name("greet")));
}

#[test]
fn test_php_imports_fold_class_and_namespace_names() {
    // namespace Lib { class Thing {} }  use LIB\THING;  use lib\thing as Alias;
    // function main(): (Thing, thing, ALIAS)   (type paths)
    let mut k = Kit::new();
    let thing = k.class("Thing", &[], &[], false);
    let lib = k.module("Lib", &[thing], Vis::Public);
    let (i1, ip1) = k.import(&["LIB", "THING"], None, Vis::Private);
    let (i2, ip2) = k.import(&["lib", "thing"], Some("Alias"), Vis::Private);
    let (t1, p1) = k.ty(&["Thing"]);
    let (t2, p2) = k.ty(&["thing"]);
    let (t3, p3) = k.ty(&["ALIAS"]);
    let b1 = k.binder("a", BinderKind::Local);
    let b2 = k.binder("b", BinderKind::Local);
    let b3 = k.binder("c", BinderKind::Local);
    let mut stmts = Vec::new();
    for (b, t) in [(b1, t1), (b2, t2), (b3, t3)] {
        let pat = k.b.bind(b);
        stmts.push(k.b.stmt(Stmt::Let {
            pat,
            ty: Some(t),
            init: None,
            else_: None,
        }));
    }
    let body = k.block(&stmts, None);
    let main = k.func("main", &[], body);
    let hir = k.finish(&[lib, i1, i2, main]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    for p in [ip1, ip2, p1, p2, p3] {
        assert_eq!(res(&r, 0, p), (item_res(0, thing), 0));
    }
}

#[test]
fn test_with_case_folds_only_the_chosen_table() {
    // A Kraken-style policy with case-insensitive types only.
    let p = Policy::new().with_case(Namespace::Type, Case::AsciiInsensitive);
    let mut k = Kit::new();
    let rec = k.record("Point", true, Vis::Private);
    let b = k.block(&[], None);
    let f = k.func("make", &[], b);
    let (t, tp) = k.ty(&["POINT"]);
    let (e, vp) = k.use_(&["MAKE"]);
    let x = k.binder("x", BinderKind::Local);
    let pat = k.b.bind(x);
    let s = k.b.stmt(Stmt::Let {
        pat,
        ty: Some(t),
        init: Some(e),
        else_: None,
    });
    let body = k.block(&[s], None);
    let main = k.func("main", &[], body);
    let hir = k.finish(&[rec, f, main]);
    let r = Resolver::new(p).resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, tp), (item_res(0, rec), 0));
    assert_eq!(res(&r, 0, vp).0, Res::Err);
    // A non-ASCII letter never folds.
    let mut k = Kit::new();
    let b = k.block(&[], None);
    let f = k.func("\u{c9}t\u{e9}", &[], b);
    let (c, p) = k.use_(&["\u{e9}t\u{e9}"]);
    let call = k.b.call(c, &[]);
    let body = k.block(&[], Some(call));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[f, main]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    assert_eq!(res(&r, 0, p).0, Res::Err);
}

// ------------------------------------------------------- differential test

const BASES: [&str; 3] = ["alpha", "beta", "gamma"];

/// A spelling of base name `b` under case mask `mask` (bit i capitalizes
/// letter i).
fn spell(b: usize, mask: u8) -> String {
    BASES[b]
        .chars()
        .enumerate()
        .map(|(i, c)| {
            if i < 8 && mask & (1 << i) != 0 {
                c.to_ascii_uppercase()
            } else {
                c
            }
        })
        .collect()
}

#[derive(Clone, Debug)]
struct Decl {
    is_fn: bool,
    base: usize,
    mask: u8,
}

#[derive(Clone, Debug)]
struct Use {
    callee: bool,
    base: usize,
    mask: u8,
}

#[derive(Clone, Debug)]
struct Prog {
    top: Vec<Decl>,
    members: Vec<Decl>,
    /// Uses in `main`: bare names.
    uses: Vec<Use>,
    /// Uses in the class's method: `self::name`.
    self_uses: Vec<Use>,
    /// Uses in `main`: `Box::name` with the class name spelled by the mask.
    class_uses: Vec<(u8, Use)>,
}

fn masks() -> impl Strategy<Value = u8> {
    prop_oneof![Just(0u8), Just(1u8), Just(0xff), any::<u8>()]
}

fn decl() -> impl Strategy<Value = Decl> {
    (any::<bool>(), 0usize..3, masks()).prop_map(|(is_fn, base, mask)| Decl { is_fn, base, mask })
}

fn use_() -> impl Strategy<Value = Use> {
    (any::<bool>(), 0usize..3, masks()).prop_map(|(callee, base, mask)| Use { callee, base, mask })
}

fn prog() -> impl Strategy<Value = Prog> {
    (
        proptest::collection::vec(decl(), 0..6),
        proptest::collection::vec(decl(), 0..5),
        proptest::collection::vec(use_(), 0..6),
        proptest::collection::vec(use_(), 0..5),
        proptest::collection::vec((masks(), use_()), 0..4),
    )
        .prop_map(|(top, members, uses, self_uses, class_uses)| Prog {
            top,
            members,
            uses,
            self_uses,
            class_uses,
        })
}

/// PHP's tables, as maps: functions by lowercased name, constants by exact
/// name, first definition kept.
#[derive(Default)]
struct Tables {
    fns: BTreeMap<String, usize>,
    consts: BTreeMap<String, usize>,
    dups: usize,
}

impl Tables {
    fn of(decls: &[Decl]) -> Self {
        let mut t = Self::default();
        for (i, d) in decls.iter().enumerate() {
            let s = spell(d.base, d.mask);
            let (map, key) = if d.is_fn {
                (&mut t.fns, s.to_ascii_lowercase())
            } else {
                (&mut t.consts, s)
            };
            match map.entry(key) {
                std::collections::btree_map::Entry::Occupied(_) => t.dups += 1,
                std::collections::btree_map::Entry::Vacant(v) => {
                    v.insert(i);
                }
            }
        }
        t
    }

    fn find(&self, u: &Use) -> Option<usize> {
        let s = spell(u.base, u.mask);
        let f = self.fns.get(&s.to_ascii_lowercase()).copied();
        let c = self.consts.get(&s).copied();
        if u.callee { f.or(c) } else { c.or(f) }
    }
}

struct Built {
    top: Vec<ItemId>,
    members: Vec<ItemId>,
    class: ItemId,
    uses: Vec<PathId>,
    self_uses: Vec<PathId>,
    class_uses: Vec<PathId>,
}

fn decl_item(k: &mut Kit, d: &Decl) -> ItemId {
    let name = spell(d.base, d.mask);
    if d.is_fn {
        let b = k.block(&[], None);
        k.func_vis(&name, &[], b, Vis::Public)
    } else {
        k.constant(&name, Vis::Public)
    }
}

fn use_expr(
    k: &mut Kit,
    parts: &[&str],
    root: PathRoot,
    callee: bool,
) -> (hir_lang::ExprId, PathId) {
    let (e, p) = k.use_root(parts, root);
    if callee {
        (k.b.call(e, &[]), p)
    } else {
        (e, p)
    }
}

fn build(k: &mut Kit, prog: &Prog) -> (hir_lang::Hir, Built) {
    let top: Vec<ItemId> = prog.top.iter().map(|d| decl_item(k, d)).collect();
    let members: Vec<ItemId> = prog.members.iter().map(|d| decl_item(k, d)).collect();
    let mut self_uses = Vec::new();
    let mut es = Vec::new();
    for u in &prog.self_uses {
        let name = spell(u.base, u.mask);
        let (e, p) = use_expr(k, &[&name], PathRoot::SelfType, u.callee);
        es.push(e);
        self_uses.push(p);
    }
    let t = k.tuple(&es);
    let mb = k.block(&[], Some(t));
    let method = k.func_vis("method_", &[], mb, Vis::Public);
    let mut items = members.clone();
    items.push(method);
    let class = k.class("Box", &[], &items, false);
    let mut uses = Vec::new();
    let mut es = Vec::new();
    for u in &prog.uses {
        let name = spell(u.base, u.mask);
        let (e, p) = use_expr(k, &[&name], PathRoot::Relative, u.callee);
        es.push(e);
        uses.push(p);
    }
    let mut class_uses = Vec::new();
    for (cm, u) in &prog.class_uses {
        let cname: String = "box"
            .chars()
            .enumerate()
            .map(|(i, c)| {
                if cm & (1 << i) != 0 {
                    c.to_ascii_uppercase()
                } else {
                    c
                }
            })
            .collect();
        let name = spell(u.base, u.mask);
        let (e, p) = use_expr(k, &[&cname, &name], PathRoot::Relative, u.callee);
        es.push(e);
        class_uses.push(p);
    }
    let t = k.tuple(&es);
    let body = k.block(&[], Some(t));
    let main = k.func("main_", &[], body);
    let mut all = top.clone();
    all.push(class);
    all.push(main);
    let hir = k.finish(&all);
    (
        hir,
        Built {
            top,
            members,
            class,
            uses,
            self_uses,
            class_uses,
        },
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn prop_php_tables_match_the_map_reference(p in prog()) {
        let mut k = Kit::new();
        let (hir, b) = build(&mut k, &p);
        let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
        let top = Tables::of(&p.top);
        let members = Tables::of(&p.members);
        for (u, &path) in p.uses.iter().zip(&b.uses) {
            let want = top.find(u).map_or(Res::Err, |i| item_res(0, b.top[i]));
            prop_assert_eq!(res(&r, 0, path).0, want, "{:?} in {:?}", u, p);
        }
        for (u, &path) in p.self_uses.iter().zip(&b.self_uses) {
            // `self::x` binds early; a miss is left to run time.
            let want = members
                .find(u)
                .map_or((Res::Unresolved, 1), |i| (item_res(0, b.members[i]), 0));
            prop_assert_eq!(res(&r, 0, path), want, "self::{:?} in {:?}", u, p);
        }
        for ((_, u), &path) in p.class_uses.iter().zip(&b.class_uses) {
            // `Box::x`: the class folds; a missing member is type-directed.
            let want = members
                .find(u)
                .map_or((item_res(0, b.class), 1), |i| (item_res(0, b.members[i]), 0));
            prop_assert_eq!(res(&r, 0, path), want, "Box::{:?} in {:?}", u, p);
        }
        let dups = kinds(&r)
            .iter()
            .filter(|d| matches!(d, DiagKind::Duplicate { .. }))
            .count();
        prop_assert_eq!(dups, top.dups + members.dups);
        prop_assert!(r.hir(hir_lang::UnitId::new(0)).unwrap().validate().is_ok());
    }

    /// Folding never changes a program whose spellings are all lowercase:
    /// under PHP, an all-lowercase program resolves like the same program
    /// under a case-sensitive copy of the policy.
    #[test]
    fn prop_folding_is_invisible_on_lowercase_programs(p in prog()) {
        let mut p = p;
        for d in p.top.iter_mut().chain(p.members.iter_mut()) {
            d.mask = 0;
        }
        for u in p.uses.iter_mut().chain(p.self_uses.iter_mut()) {
            u.mask = 0;
        }
        // The class is spelled `Box`, so `box::x` is a case variant: leave
        // class paths out here.
        p.class_uses.clear();
        let mut k = Kit::new();
        let (hir, _) = build(&mut k, &p);
        let folded = Resolver::new(Policy::php()).resolve(hir.clone(), &k.names).unwrap();
        let sensitive = Policy::php()
            .with_case(Namespace::Value, Case::Sensitive)
            .with_case(Namespace::Type, Case::Sensitive);
        let plain = Resolver::new(sensitive).resolve(hir, &k.names).unwrap();
        prop_assert_eq!(folded.hir(hir_lang::UnitId::new(0)), plain.hir(hir_lang::UnitId::new(0)));
        prop_assert_eq!(folded.diagnostics(), plain.diagnostics());
    }
}

#[test]
fn test_rename_set_includes_references_in_another_case() {
    // function Greet() {}  function main() { greet(); GREET(); }
    let mut k = Kit::new();
    let b = k.block(&[], None);
    let greet = k.func("Greet", &[], b);
    let (c1, _) = k.use_(&["greet"]);
    let call1 = k.b.call(c1, &[]);
    let (c2, _) = k.use_(&["GREET"]);
    let call2 = k.b.call(c2, &[]);
    let t = k.tuple(&[call1, call2]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[greet, main]);
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    let ix = r.index();
    let def = ix
        .definitions()
        .iter()
        .position(|d| d.name == k.name("Greet"))
        .map(resolve_lang::DefRef::from_index)
        .unwrap();
    assert_eq!(ix.references(def).count(), 2);
    // The definition plus both references.
    assert_eq!(ix.rename_set(def).edits.len(), 3);
    let _ = Ns::Value;
}
