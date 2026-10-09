//! Differential property test for the import corner: *relative* imports
//! (`use F::n as alias` written inside a module) whose first segment `F` is
//! missing from the module while its glob imports are still pending, so it
//! can only arrive through a glob, through another import, or (under
//! `ModuleScope::Lexical`) from the enclosing module. Imports may also bind
//! modules (`use super::mJ as x`), so a glob can carry the very module a
//! relative import starts from.
//!
//! The reference is a naive least fixpoint over per-table slots (the value
//! table holds functions, the module table modules), mirroring the rules:
//! definitions are one binding; a named import copies the slot its path
//! reaches (a relative first segment is looked up in the module's own
//! module-table slot, which never includes the import itself, then in the
//! enclosing module under lexical scoping); a glob joins every visible slot
//! of its target; two meanings join to ⊤.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::needless_range_loop)]

use hir_lang::{
    Builder, Def, DefId, FnDef, Item, ItemId, ItemKind, Name, Ns, Path, PathId, PathRoot, Res,
    Segment, Span, UnitId, Vis,
};
use intern_lang::Interner;
use proptest::prelude::*;
use resolve_lang::{DiagKind, ModuleScope, Policy, Resolver};

const ALL: [&str; 6] = ["a", "b", "c", "x", "y", "z"];

/// The first segment of a relative import: a name among `ALL`, or the name
/// of a sibling module (`mJ`).
#[derive(Clone, Copy, Debug)]
enum First {
    Name(usize),
    Module(usize),
}

#[derive(Clone, Copy, Debug)]
enum Target {
    /// `super::mJ::ALL[n]`
    Abs(usize, usize),
    /// `super::mJ` (binds a module)
    Module(usize),
    /// `F::ALL[n]`, relative
    Rel(First, usize),
}

#[derive(Clone, Debug)]
struct Module {
    /// a, b, c: absent, or a function, public or private.
    defs: [Option<bool>; 3],
    /// x, y, z: absent, or (target, public).
    named: [Option<(Target, bool)>; 3],
    /// (target module, public).
    globs: Vec<(usize, bool)>,
}

fn target(k: usize) -> impl Strategy<Value = Target> {
    let first = prop_oneof![
        4 => (3usize..6).prop_map(First::Name),
        1 => (0usize..3).prop_map(First::Name),
        2 => (0..k).prop_map(First::Module),
    ];
    prop_oneof![
        2 => (0..k, 0usize..6).prop_map(|(j, n)| Target::Abs(j, n)),
        2 => (0..k).prop_map(Target::Module),
        3 => (first, 0usize..6).prop_map(|(f, n)| Target::Rel(f, n)),
    ]
}

fn module(k: usize) -> impl Strategy<Value = Module> {
    (
        proptest::array::uniform3(proptest::option::weighted(0.5, any::<bool>())),
        proptest::array::uniform3(proptest::option::weighted(0.6, (target(k), any::<bool>()))),
        proptest::collection::vec((0..k, any::<bool>()), 0..3),
    )
        .prop_map(|(defs, named, globs)| Module { defs, named, globs })
}

fn graph() -> impl Strategy<Value = Vec<Module>> {
    (1usize..6).prop_flat_map(|k| proptest::collection::vec(module(k), k))
}

// --------------------------------------------------------------- reference

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Val {
    Fn(usize, usize),
    Mod(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum S {
    Absent,
    One(Val, bool),
    Top(bool),
}

fn join(a: S, b: S) -> S {
    match (a, b) {
        (S::Absent, x) | (x, S::Absent) => x,
        (S::One(t1, v1), S::One(t2, v2)) if t1 == t2 => S::One(t1, v1 || v2),
        (S::One(_, v1) | S::Top(v1), S::One(_, v2) | S::Top(v2)) => S::Top(v1 || v2),
    }
}

/// Copies a slot into an import with visibility `public`.
fn copy(s: S, public: bool) -> S {
    match s {
        S::Absent => S::Absent,
        S::One(v, _) => S::One(v, public),
        S::Top(_) => S::Top(public),
    }
}

/// Slots per module, per name, per table (0 = value, 1 = module).
type Slots = Vec<[[S; 2]; 6]>;

fn glob_val(g: &[Module], slots: &Slots, m: usize, n: usize, t: usize) -> S {
    let mut acc = S::Absent;
    for &(j, gpub) in &g[m].globs {
        let src = slots[j][n][t];
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
                S::One(v, _) => S::One(v, c),
                _ => S::Top(c),
            },
        );
    }
    acc
}

/// The least fixpoint, by naive iteration. `lexical`: a relative first
/// segment missing from the module falls back to the enclosing (root)
/// module, which defines the modules `mJ` and nothing named in `ALL`.
fn reference(g: &[Module], lexical: bool) -> Slots {
    let k = g.len();
    let mut slots: Slots = vec![[[S::Absent; 2]; 6]; k];
    loop {
        let mut next = slots.clone();
        for (m, module) in g.iter().enumerate() {
            for n in 0..6 {
                for t in 0..2 {
                    next[m][n][t] = if n < 3 && module.defs[n].is_some() {
                        if t == 0 {
                            S::One(Val::Fn(m, n), module.defs[n] == Some(true))
                        } else {
                            glob_val(g, &slots, m, n, t)
                        }
                    } else if n >= 3 && module.named[n - 3].is_some() {
                        let (tg, public) = module.named[n - 3].unwrap();
                        match tg {
                            Target::Abs(j, x) => copy(slots[j][x][t], public),
                            Target::Module(j) => {
                                if t == 1 {
                                    S::One(Val::Mod(j), public)
                                } else {
                                    S::Absent
                                }
                            }
                            Target::Rel(first, x) => {
                                // The first segment is a prefix: module table.
                                let own = match first {
                                    // An import never resolves through
                                    // itself, and its name shadows what a
                                    // glob would bring: nothing is there.
                                    First::Name(f) if f == n => S::Absent,
                                    First::Name(f) => slots[m][f][1],
                                    First::Module(_) => S::Absent,
                                };
                                let fv = match (own, first) {
                                    (S::Absent, First::Module(j)) if lexical => {
                                        S::One(Val::Mod(j), true)
                                    }
                                    _ => own,
                                };
                                match fv {
                                    S::Absent | S::One(Val::Fn(..), _) => S::Absent,
                                    S::Top(_) => S::Top(public),
                                    S::One(Val::Mod(j), _) => copy(slots[j][x][t], public),
                                }
                            }
                        }
                    } else {
                        glob_val(g, &slots, m, n, t)
                    };
                }
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
    mods: Vec<ItemId>,
    defs: Vec<[Option<ItemId>; 3]>,
    /// Import path of (module, alias index).
    imports: Vec<[Option<PathId>; 3]>,
    /// `use super::mI::n as p` in a probe module nobody imports: (module, name).
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
    let seg = |b: &mut Builder, n: Name| Segment::new(n, b.origin());
    let mut defs = Vec::new();
    let mut imports = Vec::new();
    let mut mods = Vec::new();
    for module in g {
        let mut items = Vec::new();
        let mut d = [None; 3];
        for (n, def) in module.defs.iter().enumerate() {
            let Some(public) = def else { continue };
            span(&mut b);
            let body = b.block(&[], None);
            let vis = if *public { Vis::Public } else { Vis::Private };
            let name = Name::new(names.intern(ALL[n]));
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
            let Some((tg, public)) = *named else { continue };
            let (root, parts): (PathRoot, Vec<Name>) = match tg {
                Target::Abs(j, n) => (
                    PathRoot::Super(1),
                    vec![mod_name(j, &mut names), Name::new(names.intern(ALL[n]))],
                ),
                Target::Module(j) => (PathRoot::Super(1), vec![mod_name(j, &mut names)]),
                Target::Rel(first, n) => {
                    let f = match first {
                        First::Name(f) => Name::new(names.intern(ALL[f])),
                        First::Module(j) => mod_name(j, &mut names),
                    };
                    (PathRoot::Relative, vec![f, Name::new(names.intern(ALL[n]))])
                }
            };
            let mut segs = Vec::new();
            for p in parts {
                span(&mut b);
                segs.push(seg(&mut b, p));
            }
            let segs = b.list(&segs);
            let path = b.path(Path {
                root,
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
            let s1 = seg(&mut b, mod_name(j, &mut names));
            let segs = b.list(&[s1]);
            let path = b.path(Path {
                root: PathRoot::Super(1),
                ..Path::new(segs, Ns::Import)
            });
            let vis = if public { Vis::Public } else { Vis::Private };
            items
                .push(b.item(Item::new(None, ItemKind::Import { path, glob: true }).with_vis(vis)));
        }
        defs.push(d);
        imports.push(im);
        mods.push(items);
    }
    let mut mod_items = Vec::new();
    for (m, items) in mods.into_iter().enumerate() {
        let mn = mod_name(m, &mut names);
        mod_items.push(b.module(Some(mn), &items));
    }
    // The probe module: one import per (module, name), aliased apart.
    let mut probes = Vec::new();
    let mut probe_items = Vec::new();
    for m in 0..g.len() {
        let mut row = Vec::new();
        for n in ALL {
            span(&mut b);
            let s1 = seg(&mut b, mod_name(m, &mut names));
            span(&mut b);
            let s2 = seg(&mut b, Name::new(names.intern(n)));
            let segs = b.list(&[s1, s2]);
            let path = b.path(Path {
                root: PathRoot::Super(1),
                ..Path::new(segs, Ns::Import)
            });
            let alias = Name::new(names.intern(&format!("p_{m}_{n}")));
            probe_items.push(b.item(Item::new(
                Some(alias),
                ItemKind::Import { path, glob: false },
            )));
            row.push(path);
        }
        probes.push(<[PathId; 6]>::try_from(row).unwrap());
    }
    let mut all = mod_items.clone();
    all.push(b.module(Some(Name::new(names.intern("probe"))), &probe_items));
    let root = b.module(None, &all);
    Built {
        hir: b.finish(root).expect("valid"),
        names,
        mods: mod_items,
        defs,
        imports,
        probes,
    }
}

/// What an import whose last segment reaches `slots` resolves to: the
/// value table's single meaning first, then the module table's.
fn expected(s: [S; 2], built: &Built) -> Res {
    let one = |s: S| match s {
        S::One(v, _) => Some(v),
        _ => None,
    };
    match one(s[0]).or(one(s[1])) {
        Some(Val::Fn(m, n)) => Res::Def(DefId::foreign(
            UnitId::new(0),
            Def::Item(built.defs[m][n].unwrap()),
        )),
        Some(Val::Mod(j)) => Res::Def(DefId::foreign(UnitId::new(0), Def::Item(built.mods[j]))),
        None => Res::Err,
    }
}

fn check(g: &[Module], lexical: bool) -> Result<(), TestCaseError> {
    let slots = reference(g, lexical);
    let built = build(g);
    let policy = if lexical {
        Policy::new().with_module_scope(ModuleScope::Lexical)
    } else {
        Policy::new()
    };
    let r = Resolver::new(policy)
        .resolve(built.hir.clone(), &built.names)
        .unwrap();
    let hir = r.hir(UnitId::new(0)).unwrap();
    for (m, row) in built.probes.iter().enumerate() {
        for (n, &p) in row.iter().enumerate() {
            prop_assert_eq!(
                hir.path(p).res,
                expected(slots[m][n], &built),
                "slot m{}::{} of {:?}",
                m,
                ALL[n],
                g
            );
        }
    }
    for (m, row) in built.imports.iter().enumerate() {
        for (a, p) in row.iter().enumerate() {
            let Some(p) = p else { continue };
            prop_assert_eq!(
                hir.path(*p).res,
                expected(slots[m][3 + a], &built),
                "import {} in m{} of {:?}",
                ALL[3 + a],
                m,
                g
            );
        }
    }
    // The fixpoint here is monotone (fallbacks never compete with a slot
    // that could still fill), so nothing may be reported as ambiguous after
    // the fact.
    prop_assert!(
        !r.diagnostics()
            .iter()
            .any(|d| matches!(d.kind, DiagKind::ImportAmbiguity { .. })),
        "{:?}",
        r.diagnostics()
    );
    prop_assert!(hir.validate().is_ok());
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1024))]

    #[test]
    fn prop_relative_imports_wait_for_globs_isolated(g in graph()) {
        check(&g, false)?;
    }

    #[test]
    fn prop_relative_imports_wait_for_globs_lexical(g in graph()) {
        check(&g, true)?;
    }
}

/// Guards the generator: the corner must actually occur, i.e. relative
/// imports whose first segment arrives only through a glob, and ones that
/// fall back to the enclosing module.
#[test]
fn test_generator_reaches_the_corner() {
    use proptest::strategy::ValueTree;
    use proptest::test_runner::TestRunner;
    let mut runner = TestRunner::deterministic();
    let (mut via_glob, mut fallback) = (0, 0);
    for _ in 0..400 {
        let g = graph().new_tree(&mut runner).unwrap().current();
        let slots = reference(&g, true);
        for (m, module) in g.iter().enumerate() {
            for (a, named) in module.named.iter().enumerate() {
                let Some((Target::Rel(first, _), _)) = named else {
                    continue;
                };
                match first {
                    First::Name(f) if *f != 3 + a => {
                        let own_named = *f >= 3 && module.named[*f - 3].is_some();
                        if !own_named && matches!(slots[m][*f][1], S::One(Val::Mod(_), _)) {
                            via_glob += 1;
                        }
                    }
                    First::Module(_) if !module.globs.is_empty() => fallback += 1,
                    _ => {}
                }
            }
        }
    }
    assert!(via_glob > 10 && fallback > 20, "{via_glob} {fallback}");
}

/// The worked corner: `m0 { use super::m1::*; use x::a as y; }` with
/// `m1 { pub use super::m2 as x; }` and `m2 { pub fn a }` — `x` is missing
/// from `m0` while its glob is pending, then arrives through it.
#[test]
fn test_first_segment_arrives_through_a_pending_glob() {
    let g = vec![
        Module {
            defs: [None; 3],
            named: [None, Some((Target::Rel(First::Name(3), 0), true)), None],
            globs: vec![(1, false)],
        },
        Module {
            defs: [None; 3],
            named: [Some((Target::Module(2), true)), None, None],
            globs: vec![],
        },
        Module {
            defs: [Some(true), None, None],
            named: [None; 3],
            globs: vec![],
        },
    ];
    let built = build(&g);
    let r = resolve_lang::resolve(built.hir.clone(), &built.names).unwrap();
    // Only probes of empty slots are reported.
    assert!(
        r.diagnostics().iter().all(|d| matches!(
            d.kind,
            DiagKind::Unresolved { .. } | DiagKind::Private { .. }
        )),
        "{:?}",
        r.diagnostics()
    );
    let hir = r.hir(UnitId::new(0)).unwrap();
    let want = Res::Def(DefId::foreign(
        UnitId::new(0),
        Def::Item(built.defs[2][0].unwrap()),
    ));
    assert_eq!(hir.path(built.imports[0][1].unwrap()).res, want);
    assert_eq!(hir.path(built.probes[0][4]).res, want);
}
