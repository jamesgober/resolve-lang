//! Differential property test for import resolution: random module graphs
//! with definitions, named (aliased) imports, and glob imports, public and
//! private, cycles and ambiguity included, against a naive least-fixpoint
//! reference.

// The reference indexes parallel arrays by module and name number on
// purpose: it mirrors the definition of the fixpoint.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::needless_range_loop)]

use hir_lang::{
    Builder, Def, DefId, Expr, FnDef, Item, ItemId, ItemKind, Name, Ns, Path, PathId, PathRoot,
    Res, Segment, Span, UnitId, Vis,
};
use intern_lang::Interner;
use proptest::prelude::*;

const DEFS: [&str; 3] = ["a", "b", "c"];
const ALL: [&str; 6] = ["a", "b", "c", "x", "y", "z"];

#[derive(Clone, Debug)]
struct Module {
    /// Per name in `DEFS`: absent, or defined public/private.
    defs: [Option<bool>; 3],
    /// Per alias in x, y, z: absent, or (target module, target name in ALL, public).
    named: [Option<(usize, usize, bool)>; 3],
    /// (target module, public).
    globs: Vec<(usize, bool)>,
}

fn module(k: usize) -> impl Strategy<Value = Module> {
    (
        proptest::array::uniform3(proptest::option::weighted(0.5, any::<bool>())),
        proptest::array::uniform3(proptest::option::weighted(
            0.4,
            (0..k, 0usize..6, any::<bool>()),
        )),
        proptest::collection::vec((0..k, any::<bool>()), 0..3),
    )
        .prop_map(|(defs, named, globs)| Module { defs, named, globs })
}

fn graph() -> impl Strategy<Value = Vec<Module>> {
    (1usize..6).prop_flat_map(|k| proptest::collection::vec(module(k), k))
}

// --------------------------------------------------------------- reference

/// What a slot holds: absent, one definition (module, name) with a
/// visibility (public?), or ambiguous with a visibility.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum S {
    Absent,
    One((usize, usize), bool),
    Top(bool),
}

fn join(a: S, b: S) -> S {
    match (a, b) {
        (S::Absent, x) | (x, S::Absent) => x,
        (S::One(t1, v1), S::One(t2, v2)) if t1 == t2 => S::One(t1, v1 || v2),
        (S::One(_, v1) | S::Top(v1), S::One(_, v2) | S::Top(v2)) => S::Top(v1 || v2),
    }
}

/// The least fixpoint of the import rules, by naive iteration.
fn reference(g: &[Module]) -> Vec<[S; 6]> {
    let k = g.len();
    let mut slots = vec![[S::Absent; 6]; k];
    loop {
        let mut next = slots.clone();
        for (m, module) in g.iter().enumerate() {
            for n in 0..6 {
                next[m][n] = if n < 3 && module.defs[n].is_some() {
                    S::One((m, n), module.defs[n] == Some(true))
                } else if n >= 3 && module.named[n - 3].is_some() {
                    let (j, x, public) = module.named[n - 3].unwrap();
                    match slots[j][x] {
                        S::Absent => S::Absent,
                        S::One(t, _) => S::One(t, public),
                        S::Top(_) => S::Top(public),
                    }
                } else {
                    let mut acc = S::Absent;
                    for &(j, gpub) in &module.globs {
                        let src = slots[j][n];
                        let (visible, svis) = match src {
                            S::Absent => continue,
                            S::One(_, v) | S::Top(v) => (j == m || v, v),
                        };
                        if !visible {
                            continue;
                        }
                        let c = gpub && svis;
                        acc = join(
                            acc,
                            match src {
                                S::One(t, _) => S::One(t, c),
                                _ => S::Top(c),
                            },
                        );
                    }
                    acc
                };
            }
        }
        if next == slots {
            return slots;
        }
        slots = next;
    }
}

// ------------------------------------------------------------------ build

struct Built {
    hir: hir_lang::Hir,
    names: Interner,
    /// fn item of (module, def name index).
    defs: Vec<[Option<ItemId>; 3]>,
    /// import path of (module, alias index).
    imports: Vec<[Option<PathId>; 3]>,
    /// probe path `mI::n` of (module, name index).
    probes: Vec<[PathId; 6]>,
}

fn build(g: &[Module]) -> Built {
    let mut names = Interner::new();
    let mut b = Builder::new();
    let mut pos = 0u32;
    let mut span = |b: &mut Builder| {
        pos += 2;
        b.set_span(Span::new(pos, pos + 1));
    };
    let mod_name = |i: usize, names: &mut Interner| Name::new(names.intern(&format!("m{i}")));
    let mut defs = Vec::new();
    let mut imports = Vec::new();
    let mut mods = Vec::new();
    for (m, module) in g.iter().enumerate() {
        let mut items = Vec::new();
        let mut d = [None; 3];
        for (n, def) in module.defs.iter().enumerate() {
            let Some(public) = def else { continue };
            span(&mut b);
            let body = b.block(&[], None);
            let vis = if *public { Vis::Public } else { Vis::Private };
            let name = Name::new(names.intern(DEFS[n]));
            let it = b.item(
                Item::new(
                    Some(name),
                    ItemKind::Fn(FnDef {
                        body: Some(body),
                        ..FnDef::default()
                    }),
                )
                .with_vis(vis),
            );
            d[n] = Some(it);
            items.push(it);
        }
        let mut im = [None; 3];
        for (a, named) in module.named.iter().enumerate() {
            let Some((j, x, public)) = *named else {
                continue;
            };
            span(&mut b);
            let s1 = Segment::new(mod_name(j, &mut names), b.origin());
            span(&mut b);
            let s2 = Segment::new(Name::new(names.intern(ALL[x])), b.origin());
            let segs = b.list(&[s1, s2]);
            let path = b.path(Path {
                root: PathRoot::Super(1),
                ..Path::new(segs, Ns::Import)
            });
            let alias = Name::new(names.intern(ALL[3 + a]));
            let vis = if public { Vis::Public } else { Vis::Private };
            items.push(b.item(
                Item::new(Some(alias), ItemKind::Import { path, glob: false }).with_vis(vis),
            ));
            im[a] = Some(path);
        }
        for &(j, public) in &module.globs {
            span(&mut b);
            let s1 = Segment::new(mod_name(j, &mut names), b.origin());
            let segs = b.list(&[s1]);
            let path = b.path(Path {
                root: PathRoot::Super(1),
                ..Path::new(segs, Ns::Import)
            });
            let vis = if public { Vis::Public } else { Vis::Private };
            items
                .push(b.item(Item::new(None, ItemKind::Import { path, glob: true }).with_vis(vis)));
        }
        let mn = mod_name(m, &mut names);
        mods.push(b.module(Some(mn), &items));
        defs.push(d);
        imports.push(im);
    }
    let mut probes = Vec::new();
    let mut uses = Vec::new();
    for m in 0..g.len() {
        let mut row = Vec::new();
        for n in ALL {
            span(&mut b);
            let s1 = Segment::new(mod_name(m, &mut names), b.origin());
            span(&mut b);
            let s2 = Segment::new(Name::new(names.intern(n)), b.origin());
            let segs = b.list(&[s1, s2]);
            let p = b.path(Path::new(segs, Ns::Value));
            uses.push(b.expr(Expr::Path(p)));
            row.push(p);
        }
        probes.push(<[PathId; 6]>::try_from(row).unwrap());
    }
    let list = b.list(&uses);
    let tuple = b.expr(Expr::Tuple(list));
    let body = b.block(&[], Some(tuple));
    let main = b.func(Name::new(names.intern("main")), &[], body);
    mods.push(main);
    let root = b.module(None, &mods);
    Built {
        hir: b.finish(root).expect("valid"),
        names,
        defs,
        imports,
        probes,
    }
}

fn expected(s: S, built: &Built) -> Res {
    match s {
        S::One((m, n), _) => Res::Def(DefId::foreign(
            UnitId::new(0),
            Def::Item(built.defs[m][n].unwrap()),
        )),
        _ => Res::Err,
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(768))]

    #[test]
    fn prop_imports_reach_the_least_fixpoint(g in graph()) {
        let slots = reference(&g);
        let built = build(&g);
        let r = resolve_lang::resolve(built.hir.clone(), &built.names).unwrap();
        let hir = r.hir(UnitId::new(0)).unwrap();
        for (m, row) in built.probes.iter().enumerate() {
            for (n, &p) in row.iter().enumerate() {
                prop_assert_eq!(
                    hir.path(p).res,
                    expected(slots[m][n], &built),
                    "probe m{}::{} of {:?}", m, ALL[n], g
                );
            }
        }
        for (m, row) in built.imports.iter().enumerate() {
            for (a, p) in row.iter().enumerate() {
                let Some(p) = p else { continue };
                prop_assert_eq!(
                    hir.path(*p).res,
                    expected(slots[m][3 + a], &built),
                    "import {} in m{} of {:?}", ALL[3 + a], m, g
                );
            }
        }
        prop_assert!(hir.validate().is_ok());
    }

    /// Declaration order of modules and of their items does not matter.
    #[test]
    fn prop_import_resolution_ignores_module_order(g in graph(), rot in 0usize..6) {
        let k = g.len();
        let rot = rot % k;
        // Rotate module numbering: module i becomes (i + rot) % k.
        let map = |i: usize| (i + rot) % k;
        let mut h: Vec<Module> = vec![g[0].clone(); k];
        for (i, module) in g.iter().enumerate() {
            let mut moved = module.clone();
            for n in moved.named.iter_mut().flatten() {
                n.0 = map(n.0);
            }
            for gl in &mut moved.globs {
                gl.0 = map(gl.0);
            }
            moved.globs.reverse();
            h[map(i)] = moved;
        }
        let a = build(&g);
        let b = build(&h);
        let ra = resolve_lang::resolve(a.hir.clone(), &a.names).unwrap();
        let rb = resolve_lang::resolve(b.hir.clone(), &b.names).unwrap();
        let ha = ra.hir(UnitId::new(0)).unwrap();
        let hb = rb.hir(UnitId::new(0)).unwrap();
        let describe = |hir: &hir_lang::Hir, built: &Built, p: PathId, renumber: &dyn Fn(usize) -> usize| {
            match hir.path(p).res {
                Res::Def(d) => {
                    let Def::Item(it) = d.def() else { return None };
                    built.defs.iter().enumerate().find_map(|(m, row)| {
                        row.iter().position(|x| *x == Some(it)).map(|n| (renumber(m), n))
                    })
                }
                _ => None,
            }
        };
        for m in 0..k {
            for n in 0..6 {
                let da = describe(ha, &a, a.probes[m][n], &|i| map(i));
                let db = describe(hb, &b, b.probes[map(m)][n], &|i| i);
                prop_assert_eq!(da, db, "m{}::{}", m, ALL[n]);
            }
        }
    }
}
