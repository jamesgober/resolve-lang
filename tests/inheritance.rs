//! Inheritance: C3 method resolution order for several bases (Python's
//! rule, inconsistent hierarchies reported), and unqualified names inside a
//! class seeing inherited members (`ClassScope::Lexical`). Checked against a
//! textbook C3 reference on random hierarchies, plus worked examples.

// The reference indexes parallel arrays by class and member number on
// purpose: it mirrors the definition of C3.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::needless_range_loop)]

mod common;

use common::{Kit, item_res, kinds, messages, res};
use hir_lang::{BinderKind, ItemId, PathId, Res, TyId, Vis};
use proptest::prelude::*;
use resolve_lang::{ClassScope, DiagKind, Policy, Resolver};

// ------------------------------------------------------------ worked cases

/// const x = 0; class A { protected const x; }  class B : A { fn m() { x } }
/// class C : A { const x; fn m() { x } }  class D { fn m() { x } }
/// class E : A { fn m(x) { x } }
#[test]
fn test_lexical_class_scope_sees_inherited_members() {
    let mut k = Kit::new();
    let top_x = k.constant("x", Vis::Private);
    let a_x = k.constant("x", Vis::Protected);
    let a = k.class("A", &[], &[a_x], false);
    let method = |k: &mut Kit, class: &str, own: &[ItemId], param: bool, base: bool| {
        let (u, p) = k.use_(&["x"]);
        let params: Vec<_> = if param {
            vec![k.param("x").0]
        } else {
            Vec::new()
        };
        let body = k.block(&[], Some(u));
        let m = k.func("m", &params, body);
        let bases: Vec<TyId> = if base {
            vec![k.ty(&["A"]).0]
        } else {
            Vec::new()
        };
        let mut items = own.to_vec();
        items.push(m);
        (k.class(class, &bases, &items, false), p)
    };
    let (b, pb) = method(&mut k, "B", &[], false, true);
    let c_x = k.constant("x", Vis::Private);
    let (c, pc) = method(&mut k, "C", &[c_x], false, true);
    let (d, pd) = method(&mut k, "D", &[], false, false);
    let (e, pe) = method(&mut k, "E", &[], true, true);
    let hir = k.finish(&[top_x, a, b, c, d, e]);
    let r = Resolver::new(Policy::kraken())
        .resolve(hir, &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(
        res(&r, 0, pb),
        (item_res(0, a_x), 0),
        "inherited beats outer"
    );
    assert_eq!(res(&r, 0, pc), (item_res(0, c_x), 0), "own beats inherited");
    assert_eq!(res(&r, 0, pd), (item_res(0, top_x), 0), "no base: outer");
    assert!(
        matches!(res(&r, 0, pe).0, Res::Local(_)),
        "locals beat members"
    );
}

/// const y = 0; class P { private const y; }  class Q : P { fn m() { y } }
/// A base's private member is not inherited: `y` is the module's.
#[test]
fn test_private_base_members_are_not_inherited() {
    let mut k = Kit::new();
    let top_y = k.constant("y", Vis::Private);
    let p_y = k.constant("y", Vis::Private);
    let p = k.class("P", &[], &[p_y], false);
    let (u, path) = k.use_(&["y"]);
    let body = k.block(&[], Some(u));
    let m = k.func("m", &[], body);
    let (tp, _) = k.ty(&["P"]);
    let q = k.class("Q", &[tp], &[m], false);
    let hir = k.finish(&[top_y, p, q]);
    let r = Resolver::new(Policy::kraken())
        .resolve(hir, &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, path), (item_res(0, top_y), 0));
}

/// trait T { const z; }  class U { use T; fn m() { z } }   (Lexical policy)
/// Mixin members are inherited too; and a bare identifier pattern names an
/// inherited constant.
#[test]
fn test_lexical_class_scope_sees_mixin_members_and_matches_patterns() {
    let mut k = Kit::new();
    let t_z = k.constant("Z", Vis::Public);
    let t = k.class("T", &[], &[t_z], true);
    let (ty_t, _) = k.ty(&["T"]);
    let use_t = k.mixin_use(&[ty_t], &[]);
    let (u, pz) = k.use_(&["Z"]);
    let scrut = k.b.int(1);
    let (pat, binder, ppat) = k.ident_pat("Z");
    let (other, _, _) = k.ident_pat("other");
    let one = k.b.int(1);
    let two = k.b.int(2);
    let mt = k.matches(scrut, &[(pat, one), (other, two)]);
    let tup = k.tuple(&[u, mt]);
    let body = k.block(&[], Some(tup));
    let m = k.func("m", &[], body);
    let class = k.class("U", &[], &[use_t, m], false);
    let hir = k.finish(&[t, class]);
    let r = Resolver::new(Policy::kraken())
        .resolve(hir, &k.names)
        .unwrap();
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(res(&r, 0, pz), (item_res(0, t_z), 0));
    assert_eq!(res(&r, 0, ppat), (item_res(0, t_z), 0));
    assert_eq!(r.units()[0].ident_binds(pat), Some(false));
    let _ = (binder, BinderKind::Local);
}

/// Under `BodyOnly` (Python) and `Qualified` (PHP) nothing is lexical, so
/// inheritance changes nothing there.
#[test]
fn test_inherited_members_stay_qualified_under_other_class_scopes() {
    for scope in [ClassScope::BodyOnly, ClassScope::Qualified] {
        let mut k = Kit::new();
        let top_x = k.constant("x", Vis::Public);
        let a_x = k.constant("x", Vis::Public);
        let a = k.class("A", &[], &[a_x], false);
        let (u, p) = k.use_(&["x"]);
        let body = k.block(&[], Some(u));
        let m = k.func("m", &[], body);
        let (ta, _) = k.ty(&["A"]);
        let b = k.class("B", &[ta], &[m], false);
        let hir = k.finish(&[top_x, a, b]);
        let r = Resolver::new(Policy::new().with_class_scope(scope))
            .resolve(hir, &k.names)
            .unwrap();
        assert_eq!(res(&r, 0, p), (item_res(0, top_x), 0), "{scope:?}");
    }
}

/// class O; class X(O); class Y(O); class A(X, Y); class B(Y, X); class Z(A, B)
/// — Python rejects Z ("cannot create a consistent MRO").
#[test]
fn test_python_reports_inconsistent_mro_like_class_creation() {
    let mut k = Kit::new();
    let o = k.class("O", &[], &[], false);
    let sub = |k: &mut Kit, name: &str, bases: &[&str]| {
        let tys: Vec<TyId> = bases.iter().map(|b| k.ty(&[b]).0).collect();
        k.class(name, &tys, &[], false)
    };
    let x = sub(&mut k, "X", &["O"]);
    let y = sub(&mut k, "Y", &["O"]);
    let a = sub(&mut k, "A", &["X", "Y"]);
    let b = sub(&mut k, "B", &["Y", "X"]);
    let z = sub(&mut k, "Z", &["A", "B"]);
    let hir = k.finish(&[o, x, y, a, b, z]);
    let r = Resolver::new(Policy::python())
        .resolve(hir, &k.names)
        .unwrap();
    let ks = kinds(&r);
    assert_eq!(ks, [DiagKind::InconsistentMro { class: k.name("Z") }]);
    assert_eq!(
        messages(&r, &k.names),
        ["cannot create a consistent method resolution order (MRO) for the bases of `Z`"]
    );
}

// ------------------------------------------------------- differential test

const MEMBERS: [&str; 4] = ["x", "y", "z", "w"];

#[derive(Clone, Debug)]
struct Class {
    bases: Vec<usize>,
    /// Per name in x, y, z: absent, or (0 public, 1 protected, 2 private).
    members: [Option<u8>; 3],
}

#[derive(Clone, Debug)]
struct Prog {
    classes: Vec<Class>,
    /// Module constants among x, y, z, w.
    top: [bool; 4],
}

fn prog() -> impl Strategy<Value = Prog> {
    (1usize..7).prop_flat_map(|n| {
        let class = |i: usize| {
            (
                proptest::collection::vec(0..i.max(1), 0..4),
                proptest::array::uniform3(proptest::option::weighted(0.4, 0u8..3)),
            )
                .prop_map(move |(bases, members)| {
                    let mut seen = Vec::new();
                    for b in bases {
                        // Mostly distinct bases; an occasional repeat makes
                        // an inconsistent hierarchy on purpose.
                        if b < i && (!seen.contains(&b) || b == 0) {
                            seen.push(b);
                        }
                    }
                    Class {
                        bases: seen,
                        members,
                    }
                })
        };
        let classes: Vec<_> = (0..n).map(class).collect();
        (classes, proptest::array::uniform4(any::<bool>()))
            .prop_map(|(classes, top)| Prog { classes, top })
    })
}

/// The C3 linearization of class `c` (itself first), by the textbook
/// recursive merge; an inconsistent class falls back to its bases' orders
/// concatenated without repeats. Returns the order and whether `c` itself
/// was consistent.
fn c3(p: &Prog, c: usize, memo: &mut Vec<Option<(Vec<usize>, bool)>>) -> (Vec<usize>, bool) {
    if let Some(done) = &memo[c] {
        return done.clone();
    }
    let bases = &p.classes[c].bases;
    let result = if bases.len() < 2 {
        let mut out = vec![c];
        if let Some(&b) = bases.first() {
            out.extend(c3(p, b, memo).0);
        }
        (out, true)
    } else {
        let mut lists: Vec<Vec<usize>> = bases.iter().map(|&b| c3(p, b, memo).0).collect();
        lists.push(bases.clone());
        let mut out = vec![c];
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
        if ok {
            (out, true)
        } else {
            let mut out = vec![c];
            for &b in bases {
                for x in c3(p, b, memo).0 {
                    if !out.contains(&x) {
                        out.push(x);
                    }
                }
            }
            (out, false)
        }
    };
    memo[c] = Some(result.clone());
    result
}

struct Built {
    classes: Vec<ItemId>,
    /// Per class, per name x/y/z: the member item.
    members: Vec<[Option<ItemId>; 3]>,
    top: [Option<ItemId>; 4],
    /// Per class, per name x/y/z/w: the bare use inside its method.
    lexical: Vec<[PathId; 4]>,
    /// Per class, per name x/y/z: `Ci::name` from `main`.
    qualified: Vec<[PathId; 3]>,
}

fn build(k: &mut Kit, p: &Prog) -> (hir_lang::Hir, Built) {
    let mut items = Vec::new();
    let mut top = [None; 4];
    for (n, &t) in p.top.iter().enumerate() {
        if t {
            let it = k.constant(MEMBERS[n], Vis::Private);
            top[n] = Some(it);
            items.push(it);
        }
    }
    let mut classes = Vec::new();
    let mut members = Vec::new();
    let mut lexical = Vec::new();
    for (i, c) in p.classes.iter().enumerate() {
        let mut own = Vec::new();
        let mut m = [None; 3];
        for (n, vis) in c.members.iter().enumerate() {
            let Some(v) = vis else { continue };
            let vis = [Vis::Public, Vis::Protected, Vis::Private][*v as usize];
            let it = k.constant(MEMBERS[n], vis);
            m[n] = Some(it);
            own.push(it);
        }
        let mut uses = Vec::new();
        let mut paths = Vec::new();
        for name in MEMBERS {
            let (u, path) = k.use_(&[name]);
            uses.push(u);
            paths.push(path);
        }
        let t = k.tuple(&uses);
        let body = k.block(&[], Some(t));
        own.push(k.func("method", &[], body));
        let bases: Vec<TyId> = c
            .bases
            .iter()
            .map(|b| k.ty(&[&format!("C{b}")]).0)
            .collect();
        let class = k.class(&format!("C{i}"), &bases, &own, false);
        classes.push(class);
        members.push(m);
        lexical.push(<[PathId; 4]>::try_from(paths).unwrap());
        items.push(class);
    }
    let mut qualified = Vec::new();
    let mut uses = Vec::new();
    for i in 0..p.classes.len() {
        let mut row = Vec::new();
        for name in &MEMBERS[..3] {
            let (u, path) = k.use_(&[&format!("C{i}"), name]);
            uses.push(u);
            row.push(path);
        }
        qualified.push(<[PathId; 3]>::try_from(row).unwrap());
    }
    let t = k.tuple(&uses);
    let body = k.block(&[], Some(t));
    items.push(k.func("main", &[], body));
    let hir = k.finish(&items);
    (
        hir,
        Built {
            classes,
            members,
            top,
            lexical,
            qualified,
        },
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// Kraken (lexical class scope, visibility enforced): a bare name in a
    /// method is the class's own member, else the first non-private member
    /// in C3 order, else the module's; `Ci::n` is the first member in C3
    /// order, else left to type-directed resolution.
    #[test]
    fn prop_lexical_inheritance_follows_c3(p in prog()) {
        let mut k = Kit::new();
        let (hir, b) = build(&mut k, &p);
        let r = Resolver::new(Policy::kraken()).resolve(hir, &k.names).unwrap();
        let mut memo = vec![None; p.classes.len()];
        let mut inconsistent = 0;
        for i in 0..p.classes.len() {
            let (order, ok) = c3(&p, i, &mut memo);
            inconsistent += usize::from(!ok);
            for n in 0..4 {
                let member = |c: usize, any: bool| {
                    let m = *p.classes[c].members.get(n)?;
                    let vis = m?;
                    (any || vis != 2).then(|| b.members[c][n].unwrap())
                };
                // A base's private member is not inherited: the search goes
                // on past it.
                let want = member(i, true)
                    .or_else(|| order[1..].iter().find_map(|&c| member(c, false)))
                    .or(b.top[n]);
                let want = want.map_or(Res::Err, |it| item_res(0, it));
                prop_assert_eq!(res(&r, 0, b.lexical[i][n]).0, want, "C{} {} in {:?}", i, MEMBERS[n], p);
            }
            for n in 0..3 {
                let want = order.iter().find_map(|&c| b.members[c][n]);
                let want = want.map_or((item_res(0, b.classes[i]), 1), |it| (item_res(0, it), 0));
                prop_assert_eq!(res(&r, 0, b.qualified[i][n]), want, "C{}::{} in {:?}", i, MEMBERS[n], p);
            }
        }
        let reported = kinds(&r)
            .iter()
            .filter(|d| matches!(d, DiagKind::InconsistentMro { .. }))
            .count();
        prop_assert_eq!(reported, inconsistent);
        prop_assert!(r.hir(hir_lang::UnitId::new(0)).unwrap().validate().is_ok());
    }

    /// Python (one table, body-only class scope, no visibility): `Ci::n`
    /// follows C3 the same way, private members included.
    #[test]
    fn prop_python_member_lookup_follows_c3(p in prog()) {
        let mut k = Kit::new();
        let (hir, b) = build(&mut k, &p);
        let r = Resolver::new(Policy::python()).resolve(hir, &k.names).unwrap();
        let mut memo = vec![None; p.classes.len()];
        for i in 0..p.classes.len() {
            let (order, _) = c3(&p, i, &mut memo);
            for n in 0..3 {
                let want = order.iter().find_map(|&c| b.members[c][n]);
                let want = want.map_or((item_res(0, b.classes[i]), 1), |it| (item_res(0, it), 0));
                prop_assert_eq!(res(&r, 0, b.qualified[i][n]), want, "C{}::{} in {:?}", i, MEMBERS[n], p);
            }
        }
    }
}

#[test]
fn test_generator_makes_inconsistent_and_diamond_hierarchies() {
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;
    let mut runner = TestRunner::deterministic();
    let (mut bad, mut multi) = (0, 0);
    for _ in 0..400 {
        let p = prog().new_tree(&mut runner).unwrap().current();
        let mut memo = vec![None; p.classes.len()];
        for i in 0..p.classes.len() {
            multi += usize::from(p.classes[i].bases.len() > 1);
            bad += usize::from(!c3(&p, i, &mut memo).1);
        }
    }
    assert!(bad > 10 && multi > 100, "{bad} {multi}");
}
