//! Did-you-mean suggestions: closest visible name, bounded distance,
//! budgeted.

#![allow(clippy::unwrap_used, clippy::expect_used)]

mod common;

use common::{Kit, messages};
use hir_lang::{Res, Vis};
use resolve_lang::{Budget, DefKind, Export, MapEnv, Namespace, Policy, Resolver};

#[test]
fn test_suggests_local_binder() {
    let mut k = Kit::new();
    let (p, _) = k.param("counter");
    let (u, _) = k.use_(&["countr"]);
    let body = k.block(&[], Some(u));
    let f = k.func("f", &[p], body);
    let hir = k.finish(&[f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(
        messages(&r, &k.names),
        ["cannot find value `countr` in this scope; did you mean `counter`?"]
    );
}

#[test]
fn test_does_not_suggest_unreachable_locals() {
    // fn f() { let total = 1; fn g() { totl } }  — `total` is behind a frame.
    let mut k = Kit::new();
    let one = k.b.int(1);
    let (s, _) = k.let_("total", Some(one));
    let (u, _) = k.use_(&["totl"]);
    let gb = k.block(&[], Some(u));
    let g = k.func("g", &[], gb);
    let si = k.item_stmt(g);
    let body = k.block(&[s, si], None);
    let f = k.func("f", &[], body);
    let hir = k.finish(&[f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(
        messages(&r, &k.names),
        ["cannot find value `totl` in this scope"]
    );
}

#[test]
fn test_suggests_items_and_prelude() {
    let mut k = Kit::new();
    let (u1, _) = k.use_(&["prnt"]);
    let (u2, _) = k.use_(&["helpr"]);
    let t = k.tuple(&[u1, u2]);
    let body = k.block(&[], Some(t));
    let main = k.func("main", &[], body);
    let hb = k.block(&[], None);
    let helper = k.func_vis("helper", &[], hb, Vis::Public);
    let hir = k.finish(&[main, helper]);
    let print = k.name("print");
    let env = MapEnv::new().with_prelude(
        print,
        Namespace::Value,
        Export::new(Res::Extern(print.sym), DefKind::Extern),
    );
    let r = Resolver::new(Policy::new())
        .with_env(&env)
        .resolve(hir, &k.names)
        .unwrap();
    assert_eq!(
        messages(&r, &k.names),
        [
            "cannot find value `prnt` in this scope; did you mean `print`?",
            "cannot find value `helpr` in this scope; did you mean `helper`?",
        ]
    );
}

#[test]
fn test_no_suggestion_when_too_far() {
    let mut k = Kit::new();
    let (p, _) = k.param("alpha");
    let (u, _) = k.use_(&["omega"]);
    let body = k.block(&[], Some(u));
    let f = k.func("f", &[p], body);
    let hir = k.finish(&[f]);
    let r = resolve_lang::resolve(hir, &k.names).unwrap();
    assert_eq!(r.diagnostics()[0].kind.suggestion(), None);
}

#[test]
fn test_zero_budget_still_reports_without_suggestion() {
    let mut k = Kit::new();
    let (p, _) = k.param("counter");
    let (u, _) = k.use_(&["countr"]);
    let body = k.block(&[], Some(u));
    let f = k.func("f", &[p], body);
    let hir = k.finish(&[f]);
    let r = Resolver::new(Policy::new())
        .with_budget(Budget::default().with_suggestion_cells(0))
        .resolve(hir, &k.names)
        .unwrap();
    assert_eq!(r.diagnostics().len(), 1);
    assert_eq!(r.diagnostics()[0].kind.suggestion(), None);
}

#[test]
fn test_many_unresolved_against_many_visible_is_bounded() {
    // 2000 module items and 2000 unresolved uses: suggestions stop when the
    // budget runs out, every use is still reported exactly once.
    let mut k = Kit::new();
    let mut items = Vec::new();
    for i in 0..2000 {
        let b = k.block(&[], None);
        items.push(k.func(&format!("item_{i:05}"), &[], b));
    }
    let mut uses = Vec::new();
    for i in 0..2000 {
        uses.push(k.use_(&[&format!("itme_{i:05}")]).0);
    }
    let t = k.tuple(&uses);
    let body = k.block(&[], Some(t));
    items.push(k.func("main", &[], body));
    let hir = k.finish(&items);
    let budget = Budget::default().with_suggestion_cells(200_000);
    let r = Resolver::new(Policy::new())
        .with_budget(budget)
        .resolve(hir, &k.names)
        .unwrap();
    assert_eq!(r.diagnostics().len(), 2000);
    let with = r
        .diagnostics()
        .iter()
        .filter(|d| d.kind.suggestion().is_some())
        .count();
    assert!(with > 0 && with < 2000, "{with}");
}
