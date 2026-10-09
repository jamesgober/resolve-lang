//! The persistent index: go-to-definition, find-references, rename sets,
//! document symbols, positions.

#![allow(clippy::unwrap_used, clippy::expect_used)]

mod common;

use common::{Kit, item_res, messages};
use hir_lang::{Def, DefId, PathRoot, Res, Span, UnitId, Vis};
use resolve_lang::{
    DefKind, Export, MapEnv, Namespace, Policy, Program, Resolver, SymbolKind, Target,
};

fn def_target(r: Res) -> Target {
    match r {
        Res::Def(d) => Target::Def(d),
        _ => unreachable!(),
    }
}

#[test]
fn test_references_and_go_to_definition() {
    // fn helper() {}  fn main() { (helper, helper) }
    let mut k = Kit::new();
    let hb = k.block(&[], None);
    let helper = k.func("helper", &[], hb);
    let (a, pa) = k.use_(&["helper"]);
    let (b, pb) = k.use_(&["helper"]);
    let t = k.tuple(&[a, b]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[helper, main]);
    let unit = hir.unit();
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    let ix = r.index();
    let d = ix.def_of(def_target(item_res(0, helper))).unwrap();
    assert_eq!(ix.resolve_at(unit, pa, 0), Some(d));
    assert_eq!(ix.resolve_at(unit, pb, 0), Some(d));
    let refs: Vec<_> = ix.references(d).collect();
    assert_eq!(refs.len(), 2);
    assert!(refs[0].location.span < refs[1].location.span);
    // Position lookup on the second use finds the same definition.
    let at = ix.at(unit, refs[1].location.span.start().to_u32()).unwrap();
    assert_eq!(at.def, d);
    assert!(!at.is_definition());
    // ... and on the definition's own name.
    let loc = ix.definition(d).unwrap().location.unwrap();
    let at = ix.at(unit, loc.span.start().to_u32()).unwrap();
    assert!(at.is_definition());
}

#[test]
fn test_rename_set_includes_imports_and_skips_alias_uses() {
    // mod m { pub fn foo() {} }
    // use m::foo;          // renamed
    // use m::foo as bar;   // `foo` renamed, `bar` kept
    // fn main() { (foo, bar, m::foo) }
    let mut k = Kit::new();
    let fb = k.block(&[], None);
    let foo = k.func_vis("foo", &[], fb, Vis::Public);
    let m = k.module("m", &[foo], Vis::Private);
    let (i1, _) = k.import(&["m", "foo"], None, Vis::Private);
    let (i2, _) = k.import(&["m", "foo"], Some("bar"), Vis::Private);
    let (a, _) = k.use_(&["foo"]);
    let (b, pb) = k.use_(&["bar"]);
    let (c, _) = k.use_(&["m", "foo"]);
    let t = k.tuple(&[a, b, c]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir = k.finish(&[m, i1, i2, main]);
    let unit = hir.unit();
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    let ix = r.index();
    let d = ix.def_of(def_target(item_res(0, foo))).unwrap();
    // References: two import segments, `foo`, `bar`, and `m::foo`'s last segment.
    assert_eq!(ix.references(d).len(), 5);
    let set = ix.rename_set(d);
    // Definition + 2 import segments + `foo` + `m::foo` (not `bar`).
    assert_eq!(set.edits.len(), 5, "{:?}", set.edits);
    assert!(set.outside_source.is_empty());
    // The alias is its own definition: renaming `bar` edits the alias and its use.
    let alias = ix.def_of(Target::Import(unit, i2)).unwrap();
    assert_eq!(ix.definition(alias).unwrap().kind, SymbolKind::Import);
    let set = ix.rename_set(alias);
    assert_eq!(set.edits.len(), 2);
    let use_bar = ix.path_references(unit, pb);
    assert_eq!(use_bar[0].via, Some(alias));
    assert_eq!(use_bar[0].def, d);
}

#[test]
fn test_rename_set_of_local() {
    let mut k = Kit::new();
    let (p, x) = k.param("x");
    let (a, _) = k.use_(&["x"]);
    let (b, _) = k.use_(&["x"]);
    let t = k.tuple(&[a, b]);
    let body = k.block(&[], Some(t));
    let f = k.func("f", &[p], body);
    let hir = k.finish(&[f]);
    let unit = hir.unit();
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    let d = r.index().def_of(Target::Local(unit, x)).unwrap();
    assert_eq!(r.index().definition(d).unwrap().kind, SymbolKind::Param);
    assert_eq!(r.index().rename_set(d).edits.len(), 3);
}

#[test]
fn test_document_symbols_tree() {
    // mod m { fn f() {} enum E { A, B } }  fn main() {}
    let mut k = Kit::new();
    let fb = k.block(&[], None);
    let f = k.func("f", &[], fb);
    let (e, _) = k.sum("E", &[("A", true), ("B", true)], Vis::Private);
    let m = k.module("m", &[f, e], Vis::Private);
    let mb = k.block(&[], None);
    let main = k.func("main", &[], mb);
    let hir = k.finish(&[m, main]);
    let unit = hir.unit();
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    let syms = r.index().document_symbols(unit);
    let shape: Vec<(String, SymbolKind, Option<usize>)> = syms
        .iter()
        .map(|(_, d)| {
            (
                k.names.resolve(d.name.sym).unwrap().to_string(),
                d.kind,
                d.parent
                    .map(|p| syms.iter().position(|(x, _)| *x == p).unwrap()),
            )
        })
        .collect();
    assert_eq!(
        shape,
        [
            ("m".to_string(), SymbolKind::Module, None),
            ("f".to_string(), SymbolKind::Function, Some(0)),
            ("E".to_string(), SymbolKind::Sum, Some(0)),
            ("A".to_string(), SymbolKind::Variant, Some(2)),
            ("B".to_string(), SymbolKind::Variant, Some(2)),
            ("main".to_string(), SymbolKind::Function, None),
        ]
    );
}

#[test]
fn test_cross_unit_references_and_externals() {
    // unit 1 `lib`: pub fn f() {}     unit 2: fn main() { (lib::f, print) }  print from the prelude
    let mut k = Kit::for_unit(1, intern_lang::Interner::new());
    let fb = k.block(&[], None);
    let f = k.func_vis("f", &[], fb, Vis::Public);
    let hir1 = k.finish(&[f]);
    k.start_unit(2);
    let (a, pa) = k.use_(&["lib", "f"]);
    let (b, pb) = k.use_(&["print"]);
    let t = k.tuple(&[a, b]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hir2 = k.finish(&[main]);
    let (lib, print) = (k.name("lib"), k.name("print"));
    let env = MapEnv::new().with_prelude(
        print,
        Namespace::Value,
        Export::new(Res::Extern(print.sym), DefKind::Extern),
    );
    let mut program = Program::new(Policy::new()).with_env(&env);
    program.add_unit(Some(lib), hir1);
    program.add_unit(None, hir2);
    let r = program.resolve(&k.names).unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    let ix = r.index();
    let u2 = UnitId::new(2);
    let fd = ix.resolve_at(u2, pa, 1).unwrap();
    assert_eq!(
        ix.definition(fd).unwrap().target,
        Target::Def(DefId::foreign(UnitId::new(1), Def::Item(f)))
    );
    // `lib` itself is a reference to unit 1's root module (unnamed: no definition).
    assert_eq!(ix.resolve_at(u2, pa, 0), None);
    let pd = ix.resolve_at(u2, pb, 0).unwrap();
    let pdef = ix.definition(pd).unwrap();
    assert_eq!(pdef.kind, SymbolKind::External);
    assert!(pdef.location.is_none());
    assert_eq!(ix.def_of(Target::Extern(print.sym)), Some(pd));
}

#[test]
fn test_expanded_names_are_outside_source() {
    use hir_lang::{Expansion, ExpnKind, Origin};
    let mut k = Kit::new();
    let (p, x) = k.param("x");
    let mac = k.name("mac").sym;
    let expn = k.b.expansion(Expansion {
        kind: ExpnKind::Macro,
        name: mac,
        call_site: Span::new(500, 510),
        parent: hir_lang::ExpnId::ROOT,
        def_site: hir_lang::ExpnId::ROOT,
    });
    k.b.set_origin(Origin::expanded(Span::new(1, 2), expn));
    let xn = k.name("x");
    let seg = hir_lang::Segment::new(xn, k.b.origin());
    let segs = k.b.list(&[seg]);
    let path = k.b.path(hir_lang::Path::new(segs, hir_lang::Ns::Value));
    let use_x = k.b.expr(hir_lang::Expr::Path(path));
    k.b.set_origin(Origin::new(Span::new(600, 601)));
    let body = k.block(&[], Some(use_x));
    let f = k.func("f", &[p], body);
    let hir = k.finish(&[f]);
    let unit = hir.unit();
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    let d = r.index().def_of(Target::Local(unit, x)).unwrap();
    let set = r.index().rename_set(d);
    assert_eq!(set.edits.len(), 1);
    assert_eq!(set.outside_source.len(), 1);
    assert_eq!(set.outside_source[0].span, Span::new(500, 510));
}

#[test]
fn test_member_references_are_indexed() {
    // class C { const K = 1; function m() { self::K } }
    let mut k = Kit::new();
    let kc = k.constant("K", Vis::Public);
    let (e, p) = k.use_root(&["K"], PathRoot::SelfType);
    let mb = k.block(&[], Some(e));
    let m = k.func_vis("m", &[], mb, Vis::Public);
    let c = k.class("C", &[], &[kc, m], false);
    let hir = k.finish(&[c]);
    let unit = hir.unit();
    let r = Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap();
    let d = r.index().def_of(def_target(item_res(0, kc))).unwrap();
    assert_eq!(r.index().resolve_at(unit, p, 0), Some(d));
    assert_eq!(r.index().references(d).len(), 1);
}
