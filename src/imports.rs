//! Phase 2: resolve every import of the program, jointly.
//!
//! Imports can depend on each other across modules and units, in cycles, and
//! through glob imports, so they are resolved as a monotone fixpoint rather
//! than in any fixed order.
//!
//! Every (scope, namespace, name) *slot* only ever moves up a three-step
//! lattice: absent, then one binding, then ambiguous (⊤). Definitions are one
//! binding from the start. A named import's slot is a copy of the slot its
//! path reaches (⊤ if any step of the path is ⊤); a glob import joins every
//! visible slot of its target into its own scope (two different meanings
//! join to ⊤), and its visibility only grows. Because every rule is monotone,
//! the result is the least fixpoint, independent of the order imports are
//! visited in:
//!
//! - An import whose path reaches an absent slot that could still be filled
//!   *waits* on that (scope, name) pair and is woken when the slot fills.
//! - A resolved import subscribes to the slots its path went through; if one
//!   of them becomes ⊤ the import is re-evaluated and becomes ⊤ too, and that
//!   propagates like any other change.
//! - Glob propagation is a worklist of slot changes; each slot changes a
//!   bounded number of times, so its cost is bounded by the slots it fills,
//!   which the [`Budget`](crate::Budget) caps.
//! - When nothing can make progress, every remaining wait is on a slot that
//!   nothing will fill, except where a lexical first segment could fall back
//!   to an outer scope, a root, or the prelude. Then the lowest-numbered
//!   waiting import is settled in *final mode* (a miss in a scope with globs
//!   counts as absent, a name another waiting import binds counts as a
//!   cycle), the worklist runs again, and so on. Imports settled that way
//!   are rechecked at the end and reported if the finished tables would
//!   resolve them differently.
//!
//! Every step is deterministic: queues are FIFO in import order and every map
//! is ordered.

use alloc::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    vec::Vec,
};

use hir_lang::{Def, Name, NodeRef, PathRoot, Res, Span, Vis};
use intern_lang::Lookup;

use crate::{
    diag::DiagKind,
    env::{DefKind, env_members},
    error::{Limit, ResolveError},
    model::{
        ANY_NS, Binding, Entry, EntryState, ImportState, Model, NONE, Origin, ScopeKind,
        entry_order, ix,
    },
    policy::{Hoist, ItemClass, ModuleScope, Namespace, min_vis, vis_rank},
    suggest::{MAX_CANDIDATES, Suggester},
};

/// Something a path segment reached.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Hit {
    pub(crate) res: Res,
    pub(crate) kind: DefKind,
    pub(crate) vis: Vis,
    /// The program binding, or `NONE` (roots, variants, environment).
    pub(crate) binding: u32,
}

/// A slot's state: one binding, or ⊤ with two witnesses and the widest
/// visibility any contribution had.
#[derive(Clone, Copy, Debug)]
enum GState {
    One(u32),
    Amb { a: u32, b: u32, vis: Vis },
}

/// What a lookup found in one table.
#[derive(Clone, Copy, Debug)]
enum Slot {
    Hit(Hit),
    /// Ambiguous: two witness bindings.
    Top(u32, u32),
}

/// How a lookup treats undetermined names, and which import is asking (an
/// import never resolves through itself).
#[derive(Clone, Copy, Debug)]
struct Mode {
    final_mode: bool,
    skip: u32,
}

/// One table lookup's answer.
#[derive(Clone, Copy, Debug)]
enum L {
    Found(u32),
    Amb(u32, u32),
    Pending,
    NotFound,
    Failed,
    Cycle,
}

/// Where a glob points.
#[derive(Clone, Copy, Debug)]
enum Container {
    Scope(u32),
    Sum,
    Outside(Res),
}

/// A failure, with the segment it is about.
#[derive(Clone, Copy, Debug)]
struct Fail {
    kind: DiagKind,
    seg: usize,
    /// Where to look for suggestions.
    near: Near,
}

#[derive(Clone, Copy, Debug)]
enum Near {
    Nothing,
    Lexical(u32),
    In(Hit),
}

enum Attempt {
    Named {
        slots: Vec<(u8, Slot)>,
        deps: Vec<(u32, Name)>,
        segs: Vec<(u32, Res, u32)>,
        private: Option<(Name, Res, Vis, usize)>,
    },
    Glob {
        container: Container,
        res: Res,
        deps: Vec<(u32, Name)>,
        segs: Vec<(u32, Res, u32)>,
        private: Option<(Name, Res, Vis, usize)>,
    },
    Wait(u32, Name),
    Fail(Fail),
}

/// The outcome of one step of a path: per-table slots and the scope slot it
/// read (for subscriptions).
enum Step {
    Found(Vec<(u8, Slot)>, Option<(u32, Name)>),
    Wait(u32, Name),
    Fail(Fail),
}

/// One glob propagation: carry `src` (a binding, or the first witness of a
/// ⊤ slot) into scope `s` through glob import `g`.
#[derive(Clone, Copy, Debug)]
struct Task {
    s: u32,
    g: u32,
    src: u32,
    top: bool,
}

struct Work {
    defs: Vec<Vec<u32>>,
    named_names: Vec<Vec<(Name, u32)>>,
    named_res: Vec<BTreeMap<(u8, Name), GState>>,
    glob_res: Vec<BTreeMap<(u8, Name), GState>>,
    importers: Vec<Vec<(u32, u32)>>,
    /// Pending imports waiting for a slot to fill.
    waiters: BTreeMap<(u32, Name), Vec<u32>>,
    /// Resolved imports whose path read a slot (woken whenever it changes).
    subs: BTreeMap<(u32, Name), Vec<u32>>,
    queue: VecDeque<u32>,
    stuck: BTreeSet<u32>,
    tasks: VecDeque<Task>,
    budget: u64,
    /// Imports that ended ⊤ (named) or were found ambiguous after the fact
    /// (globs): reported once.
    top: Vec<bool>,
}

/// Resolves every import of the model and builds each scope's final table.
pub(crate) fn resolve_imports<L: Lookup>(
    m: &mut Model<'_>,
    names: &L,
    suggester: &mut Suggester,
    glob_budget: u64,
) -> Result<(), ResolveError> {
    let n = m.scopes.len();
    let mut w = Work {
        defs: Vec::with_capacity(n),
        named_names: Vec::with_capacity(n),
        named_res: (0..n).map(|_| BTreeMap::new()).collect(),
        glob_res: (0..n).map(|_| BTreeMap::new()).collect(),
        importers: (0..n).map(|_| Vec::new()).collect(),
        waiters: BTreeMap::new(),
        subs: BTreeMap::new(),
        queue: VecDeque::new(),
        stuck: BTreeSet::new(),
        tasks: VecDeque::new(),
        budget: glob_budget,
        top: alloc::vec![false; m.imports.len()],
    };
    for s in &m.scopes {
        let mut defs: Vec<u32> = s
            .defs
            .iter()
            .copied()
            .filter(|b| m.bindings.get(*b as usize).is_some_and(|b| !b.shadowed))
            .collect();
        defs.sort_by_key(|b| m.bindings.get(*b as usize).map(|b| (b.ns, b.name)));
        w.defs.push(defs);
        let mut named: Vec<(Name, u32)> = s
            .named
            .iter()
            .filter_map(|i| {
                m.imports
                    .get(*i as usize)
                    .and_then(|imp| imp.name.map(|n| (n, *i)))
            })
            .collect();
        named.sort();
        w.named_names.push(named);
    }
    for (i, imp) in m.imports.iter().enumerate() {
        if imp.state == ImportState::Pending {
            w.queue.push_back(ix(i));
        }
    }
    loop {
        while let Some(i) = w.queue.pop_front() {
            let Some(imp) = m.imports.get(i as usize) else {
                continue;
            };
            let recheck = match imp.state {
                ImportState::Pending => false,
                ImportState::Done
                    if !imp.glob || !w.top.get(i as usize).copied().unwrap_or(true) =>
                {
                    true
                }
                _ => continue,
            };
            let final_mode = recheck && imp.late;
            let attempt = attempt(m, &w, i, final_mode);
            settle(m, &mut w, names, suggester, i, attempt, final_mode, recheck)?;
        }
        let Some(i) = w.stuck.pop_first() else { break };
        if m.imports.get(i as usize).map(|imp| imp.state) != Some(ImportState::Pending) {
            continue;
        }
        let attempt = attempt(m, &w, i, true);
        settle(m, &mut w, names, suggester, i, attempt, true, false)?;
    }
    report_top(m, &w);
    recheck_late(m, &w);
    build_tables(m, &w);
    Ok(())
}

/// Applies an attempt's outcome. `recheck` marks a resolved import being
/// re-evaluated because a slot on its path turned ⊤.
#[allow(clippy::too_many_arguments)]
fn settle<L: Lookup>(
    m: &mut Model<'_>,
    w: &mut Work,
    names: &L,
    suggester: &mut Suggester,
    i: u32,
    attempt: Attempt,
    final_mode: bool,
    recheck: bool,
) -> Result<(), ResolveError> {
    match attempt {
        Attempt::Named {
            slots,
            deps,
            segs,
            private,
        } => {
            if recheck {
                return merge(m, w, i, &slots, false);
            }
            report_private(m, i, private);
            subscribe(w, i, &deps);
            install_named(m, w, i, &slots, segs, final_mode)?;
        }
        Attempt::Glob {
            container,
            res,
            deps,
            segs,
            private,
        } => {
            if recheck {
                return Ok(());
            }
            report_private(m, i, private);
            subscribe(w, i, &deps);
            install_glob(m, w, i, container, res, segs, final_mode)?;
        }
        Attempt::Wait(s, name) if !final_mode && !recheck => {
            w.waiters.entry((s, name)).or_default().push(i);
            let _new = w.stuck.insert(i);
        }
        Attempt::Wait(..) if recheck => {}
        Attempt::Wait(..) => {
            // Final mode never waits; a stray wait is treated as a cycle so
            // the loop always terminates.
            let name = m.imports.get(i as usize).and_then(|imp| imp.name);
            let kind = name.map_or(DiagKind::GlobsUnsupported, |name| DiagKind::ImportCycle {
                name,
            });
            fail(
                m,
                w,
                names,
                suggester,
                i,
                Fail {
                    kind,
                    seg: 0,
                    near: Near::Nothing,
                },
            );
        }
        Attempt::Fail(f) if recheck => {
            // A resolved glob whose module path became ambiguous keeps what
            // it imported (retracting would break monotonicity); report it.
            if matches!(f.kind, DiagKind::AmbiguousGlob { .. }) {
                if let Some(t) = w.top.get_mut(i as usize) {
                    *t = true;
                }
                let name = match f.kind {
                    DiagKind::AmbiguousGlob { name, .. } => name,
                    _ => return Ok(()),
                };
                if let Some((unit, span, path)) = seg_site(m, i, f.seg) {
                    m.report(
                        unit,
                        DiagKind::ImportAmbiguity { name },
                        span,
                        Some(NodeRef::Path(path)),
                    );
                }
            }
        }
        Attempt::Fail(f) => fail(m, w, names, suggester, i, f),
    }
    Ok(())
}

fn subscribe(w: &mut Work, i: u32, deps: &[(u32, Name)]) {
    for &d in deps {
        w.subs.entry(d).or_default().push(i);
    }
}

fn report_private(m: &mut Model<'_>, i: u32, private: Option<(Name, Res, Vis, usize)>) {
    let Some((name, res, vis, seg)) = private else {
        return;
    };
    let Some((unit, span, path)) = seg_site(m, i, seg) else {
        return;
    };
    m.report(
        unit,
        DiagKind::Private { name, res, vis },
        span,
        Some(NodeRef::Path(path)),
    );
}

/// The unit, span, and path of segment `seg` of import `i`.
fn seg_site(m: &Model<'_>, i: u32, seg: usize) -> Option<(u32, Span, hir_lang::PathId)> {
    let imp = m.imports.get(i as usize)?;
    let hir = &m.units.get(imp.unit as usize)?.hir;
    let segs = hir.list(hir.path(imp.path).segments);
    let span = segs
        .get(seg)
        .or(segs.last())
        .map_or(hir.origin(NodeRef::Path(imp.path)).span, |s| s.origin.span);
    Some((imp.unit, span, imp.path))
}

fn fail<L: Lookup>(
    m: &mut Model<'_>,
    w: &mut Work,
    names: &L,
    suggester: &mut Suggester,
    i: u32,
    mut f: Fail,
) {
    if let DiagKind::Unresolved {
        name, suggestion, ..
    } = &mut f.kind
    {
        if suggester.has_budget() {
            let mut cands = Vec::new();
            candidates(m, w, f.near, &mut cands);
            *suggestion = suggester.best(names, *name, &cands);
        }
    }
    let Some(imp) = m.imports.get_mut(i as usize) else {
        return;
    };
    imp.state = ImportState::Failed;
    imp.res = Res::Err;
    imp.unresolved = 0;
    let (scope, name) = (imp.scope, imp.name);
    let _was = w.stuck.remove(&i);
    if let Some((unit, span, path)) = seg_site(m, i, f.seg) {
        m.report(unit, f.kind, span, Some(NodeRef::Path(path)));
    }
    if let Some(name) = name {
        wake(w, scope, name);
    }
}

/// A slot of `scope` named `name` filled: wake the imports waiting for it.
fn wake(w: &mut Work, scope: u32, name: Name) {
    if let Some(list) = w.waiters.remove(&(scope, name)) {
        w.queue.extend(list);
    }
}

/// A slot of `scope` named `name` changed: re-evaluate the resolved imports
/// that read it (they may bind another table now, or turn ⊤).
fn wake_subs(w: &mut Work, scope: u32, name: Name) {
    if let Some(list) = w.subs.get(&(scope, name)) {
        w.queue.extend(list.iter().copied());
    }
}

/// Names visible near a failure, for suggestions.
fn candidates(m: &Model<'_>, w: &Work, near: Near, out: &mut Vec<Name>) {
    let push_scope = |s: u32, out: &mut Vec<Name>| {
        let scope = s as usize;
        for b in w.defs.get(scope).into_iter().flatten() {
            if let Some(b) = m.bindings.get(*b as usize) {
                out.push(b.name);
            }
        }
        for (n, _) in w.named_names.get(scope).into_iter().flatten() {
            out.push(*n);
        }
        for (_, n) in w.glob_res.get(scope).into_iter().flat_map(|g| g.keys()) {
            out.push(*n);
        }
    };
    match near {
        Near::Nothing => {}
        Near::Lexical(start) => {
            let mut s = start;
            while let Some(scope) = m.scopes.get(s as usize) {
                if out.len() >= MAX_CANDIDATES {
                    break;
                }
                if !matches!(scope.kind, ScopeKind::Type(..)) {
                    push_scope(s, out);
                }
                if matches!(scope.kind, ScopeKind::Module(_))
                    && m.policy.module_scope() == ModuleScope::Isolated
                {
                    break;
                }
                s = scope.parent;
            }
            out.extend(m.roots.iter().map(|(n, _)| *n));
            m.env.for_each_root(&mut |n| {
                if out.len() < 2 * MAX_CANDIDATES {
                    out.push(n);
                }
            });
        }
        Near::In(hit) => {
            if let Some(s) = m.scope_of(hit.res) {
                push_scope(s, out);
            } else if let Some((_, t)) = m.sum_of(hit.res) {
                for (sym, _) in m.sums.get(t as usize).into_iter().flatten() {
                    out.push(Name::new(*sym));
                }
            } else if m.is_outside(hit.res) {
                for (n, _, _) in env_members(m.env, hit.res) {
                    out.push(n);
                }
            }
        }
    }
    out.sort();
    out.dedup();
    out.truncate(MAX_CANDIDATES);
}

// ------------------------------------------------------------------ lookup

/// The table indexes a segment searches: every table for the last segment
/// of a named import, module and type tables for a prefix.
fn tables(m: &Model<'_>, all: bool) -> Vec<u8> {
    let list: &[Namespace] = if all {
        &[
            Namespace::Value,
            Namespace::Type,
            Namespace::Module,
            Namespace::Macro,
        ]
    } else {
        &[Namespace::Module, Namespace::Type]
    };
    let mut out: Vec<u8> = Vec::with_capacity(4);
    for ns in list {
        let t = m.policy.table_ix(*ns);
        if !out.contains(&t) {
            out.push(t);
        }
    }
    out
}

/// The definition of `key` in scope `s` (the last one, under `LastWins`).
fn def_in(m: &Model<'_>, w: &Work, s: u32, key: (u8, Name)) -> Option<u32> {
    let defs = w.defs.get(s as usize)?;
    let upper = defs.partition_point(|b| {
        m.bindings
            .get(*b as usize)
            .is_some_and(|b| (b.ns, b.name) <= key)
    });
    let b = *defs.get(upper.checked_sub(1)?)?;
    m.bindings
        .get(b as usize)
        .is_some_and(|x| (x.ns, x.name) == key)
        .then_some(b)
}

/// The named imports of `name` in scope `s`.
fn named_of(w: &Work, s: u32, name: Name) -> &[(Name, u32)] {
    let named = w.named_names.get(s as usize).map_or(&[][..], Vec::as_slice);
    let lo = named.partition_point(|(n, _)| *n < name);
    let hi = named.partition_point(|(n, _)| *n <= name);
    named.get(lo..hi).unwrap_or(&[])
}

const fn as_lookup(g: GState) -> L {
    match g {
        GState::One(b) => L::Found(b),
        GState::Amb { a, b, .. } => L::Amb(a, b),
    }
}

/// Looks `name` up in one table of scope `s`, during import resolution.
fn lookup(m: &Model<'_>, w: &Work, s: u32, t: u8, name: Name, mode: Mode) -> L {
    let key = (t, name);
    if let Some(b) = def_in(m, w, s, key) {
        return L::Found(b);
    }
    // An import never resolves through itself (`import os` looks past its
    // own binding of `os`).
    let same = named_of(w, s, name);
    if same.iter().any(|(_, i)| *i != mode.skip) {
        if let Some(&g) = w.named_res.get(s as usize).and_then(|r| r.get(&key)) {
            return as_lookup(g);
        }
        let state = |i: u32| m.imports.get(i as usize).map(|imp| imp.state);
        let others = || same.iter().filter(|(_, i)| *i != mode.skip);
        if others().any(|(_, i)| state(*i) == Some(ImportState::Pending)) {
            return if mode.final_mode {
                L::Cycle
            } else {
                L::Pending
            };
        }
        let failed = others().any(|(_, i)| state(*i) == Some(ImportState::Failed));
        let done = others().any(|(_, i)| state(*i) == Some(ImportState::Done));
        return if failed && !done {
            L::Failed
        } else {
            L::NotFound
        };
    }
    if let Some(&g) = w.glob_res.get(s as usize).and_then(|g| g.get(&key)) {
        return as_lookup(g);
    }
    let has_globs = m
        .scopes
        .get(s as usize)
        .is_some_and(|s| !s.globs.is_empty());
    if has_globs && !mode.final_mode {
        L::Pending
    } else {
        L::NotFound
    }
}

fn hit_of(m: &Model<'_>, b: u32) -> Option<Hit> {
    m.bindings.get(b as usize).map(|bind| Hit {
        res: bind.res,
        kind: bind.kind,
        vis: bind.vis,
        binding: b,
    })
}

/// Looks a name up in several tables of one scope. `all` collects a slot per
/// table (the last segment of a named import); otherwise the first table
/// with something wins. `None` when nothing is there.
// The lookup context is passed flat: it changes at every call site, so a
// context struct would only be rebuilt each time.
#[allow(clippy::too_many_arguments)]
fn lookup_tables(
    m: &Model<'_>,
    w: &Work,
    s: u32,
    ts: &[u8],
    name: Name,
    mode: Mode,
    all: bool,
    seg: usize,
    near: Near,
) -> Option<Step> {
    // With `all` (the last segment of a named import) every table is its own
    // monotone link: tables found now are bound now, and the import stays
    // subscribed to this (scope, name) for the tables still undetermined.
    // Otherwise the first table with anything decides, and an undetermined
    // earlier table must be waited for.
    let mut found: Vec<(u8, Slot)> = Vec::new();
    let mut pending = false;
    let mut dead: Option<Fail> = None;
    for &t in ts {
        let slot = match lookup(m, w, s, t, name, mode) {
            L::Found(b) => hit_of(m, b).map(Slot::Hit),
            L::Amb(a, b) => Some(Slot::Top(a, b)),
            L::Pending if all => {
                pending = true;
                None
            }
            L::Pending => return Some(Step::Wait(s, name)),
            l @ (L::Cycle | L::Failed) => {
                let fail = Fail {
                    kind: if matches!(l, L::Cycle) {
                        DiagKind::ImportCycle { name }
                    } else {
                        DiagKind::BrokenImport { name }
                    },
                    seg,
                    near,
                };
                if !all {
                    return Some(Step::Fail(fail));
                }
                if dead.is_none() {
                    dead = Some(fail);
                }
                None
            }
            L::NotFound => None,
        };
        if let Some(slot) = slot {
            found.push((t, slot));
            if !all {
                break;
            }
        }
    }
    if !found.is_empty() {
        return Some(Step::Found(found, Some((s, name))));
    }
    if pending {
        return Some(Step::Wait(s, name));
    }
    dead.map(Step::Fail)
}

/// A root name: a program unit, else the environment's root.
fn root_hit(m: &Model<'_>, name: Name) -> Option<Hit> {
    if let Ok(i) = m.roots.binary_search_by(|(n, _)| n.cmp(&name)) {
        let u = m.roots.get(i)?.1;
        let unit = m.units.get(u as usize)?;
        return Some(Hit {
            res: Res::Def(hir_lang::DefId::foreign(
                unit.id,
                Def::Item(unit.hir.root()),
            )),
            kind: DefKind::Module,
            vis: Vis::Public,
            binding: NONE,
        });
    }
    m.env.root(name).map(|e| Hit {
        res: e.res,
        kind: e.kind,
        vis: e.vis,
        binding: NONE,
    })
}

/// The prelude's slots for `name` in tables `ts`.
fn prelude_slots(m: &Model<'_>, name: Name, ts: &[u8], all: bool) -> Vec<(u8, Slot)> {
    let mut found = Vec::new();
    for &t in ts {
        for ns in Namespace::ALL {
            if m.policy.table_ix(ns) != t {
                continue;
            }
            if let Some(e) = m.env.prelude(name, ns) {
                found.push((
                    t,
                    Slot::Hit(Hit {
                        res: e.res,
                        kind: e.kind,
                        vis: e.vis,
                        binding: NONE,
                    }),
                ));
                break;
            }
        }
        if !all && !found.is_empty() {
            break;
        }
    }
    found
}

fn unresolved(name: Name, container: Option<Name>, seg: usize, near: Near) -> Step {
    Step::Fail(Fail {
        kind: DiagKind::Unresolved {
            name,
            ns: hir_lang::Ns::Import,
            container,
            suggestion: None,
        },
        seg,
        near,
    })
}

/// Lexical lookup of an import's first segment from scope `start`.
fn lexical(
    m: &Model<'_>,
    w: &Work,
    start: u32,
    name: Name,
    ts: &[u8],
    mode: Mode,
    all: bool,
) -> Step {
    let mut s = start;
    while let Some(scope) = m.scopes.get(s as usize) {
        if !matches!(scope.kind, ScopeKind::Type(..)) {
            if let Some(step) = lookup_tables(m, w, s, ts, name, mode, all, 0, Near::Lexical(start))
            {
                return step;
            }
        }
        if matches!(scope.kind, ScopeKind::Module(_))
            && m.policy.module_scope() == ModuleScope::Isolated
        {
            break;
        }
        s = scope.parent;
    }
    let module_table = m.policy.table_ix(Namespace::Module);
    if ts.contains(&module_table) || ts.contains(&m.policy.table_ix(Namespace::Type)) {
        if let Some(h) = root_hit(m, name) {
            return Step::Found(alloc::vec![(module_table, Slot::Hit(h))], None);
        }
    }
    let found = prelude_slots(m, name, ts, all);
    if !found.is_empty() {
        return Step::Found(found, None);
    }
    unresolved(name, None, 0, Near::Lexical(start))
}

/// One step through a container that is not ⊤.
#[allow(clippy::too_many_arguments)]
fn step(
    m: &Model<'_>,
    w: &Work,
    container: Hit,
    container_name: Name,
    name: Name,
    ts: &[u8],
    mode: Mode,
    all: bool,
    seg: usize,
) -> Step {
    if container.kind == DefKind::Module {
        if let Some(s) = m.scope_of(container.res) {
            return lookup_tables(m, w, s, ts, name, mode, all, seg, Near::In(container))
                .unwrap_or_else(|| {
                    unresolved(name, Some(container_name), seg, Near::In(container))
                });
        }
    }
    if let Some((u, t)) = m.sum_of(container.res) {
        let table = m.sums.get(t as usize).map_or(&[][..], Vec::as_slice);
        let found = name
            .mark
            .is_root()
            .then(|| table.binary_search_by(|(s, _)| s.cmp(&name.sym)).ok())
            .flatten()
            .and_then(|i| table.get(i));
        let Some(&(_, v)) = found else {
            return unresolved(name, Some(container_name), seg, Near::In(container));
        };
        let unit_variant = m
            .units
            .get(u as usize)
            .and_then(|unit| unit.hir.variant(v))
            .is_some_and(|v| v.shape == hir_lang::Shape::Unit);
        let hit = Hit {
            res: Res::Def(m.def_id(u, Def::Variant(v))),
            kind: DefKind::Variant { unit: unit_variant },
            vis: container.vis,
            binding: NONE,
        };
        let mut found: Vec<(u8, Slot)> = Vec::new();
        for ns in [Namespace::Value, Namespace::Type] {
            let t = m.policy.table_ix(ns);
            if ts.contains(&t) && !found.iter().any(|(x, _)| *x == t) {
                found.push((t, Slot::Hit(hit)));
            }
            if !all && !found.is_empty() {
                break;
            }
        }
        if found.is_empty() {
            found.push((ts.first().copied().unwrap_or(0), Slot::Hit(hit)));
        }
        return Step::Found(found, None);
    }
    if m.is_outside(container.res)
        && matches!(
            container.kind,
            DefKind::Module | DefKind::Extern | DefKind::Sum
        )
    {
        let mut found = Vec::new();
        for &t in ts {
            for ns in Namespace::ALL {
                if m.policy.table_ix(ns) != t {
                    continue;
                }
                if let Some(e) = m.env.member(container.res, name, ns) {
                    found.push((
                        t,
                        Slot::Hit(Hit {
                            res: e.res,
                            kind: e.kind,
                            vis: e.vis,
                            binding: NONE,
                        }),
                    ));
                    break;
                }
            }
            if !all && !found.is_empty() {
                break;
            }
        }
        return if found.is_empty() {
            unresolved(name, Some(container_name), seg, Near::In(container))
        } else {
            Step::Found(found, None)
        };
    }
    Step::Fail(Fail {
        kind: DiagKind::NotAContainer {
            name: container_name,
            found: container.kind,
        },
        seg: seg.saturating_sub(1),
        near: Near::Nothing,
    })
}

/// The ancestor module `levels` above `module`.
fn ancestor(m: &Model<'_>, module: u32, levels: u8) -> Option<u32> {
    let mut s = module;
    for _ in 0..levels {
        let parent = m.scopes.get(s as usize)?.parent;
        s = m.scopes.get(parent as usize)?.module;
    }
    Some(s)
}

/// The first segment's step.
fn first_step(
    m: &Model<'_>,
    w: &Work,
    i: u32,
    mode: Mode,
    ts: &[u8],
    all: bool,
) -> Result<Step, Fail> {
    let root_fail = |root: PathRoot| Fail {
        kind: DiagKind::RootUnsupported { root },
        seg: 0,
        near: Near::Nothing,
    };
    let imp = m
        .imports
        .get(i as usize)
        .ok_or(root_fail(PathRoot::Relative))?;
    let unit = m
        .units
        .get(imp.unit as usize)
        .ok_or(root_fail(PathRoot::Relative))?;
    let path = unit.hir.path(imp.path);
    let first = unit
        .hir
        .list(path.segments)
        .first()
        .ok_or(root_fail(path.root))?;
    let module = m.scopes.get(imp.scope as usize).map_or(NONE, |s| s.module);
    Ok(match path.root {
        PathRoot::Relative => lexical(m, w, imp.scope, first.name, ts, mode, all),
        PathRoot::Global => {
            let root = unit.root_scope;
            match lookup_tables(
                m,
                w,
                root,
                ts,
                first.name,
                mode,
                all,
                0,
                Near::Lexical(root),
            ) {
                Some(step) => step,
                None => match root_hit(m, first.name) {
                    Some(h) => Step::Found(
                        alloc::vec![(m.policy.table_ix(Namespace::Module), Slot::Hit(h))],
                        None,
                    ),
                    None => unresolved(first.name, None, 0, Near::Lexical(root)),
                },
            }
        }
        PathRoot::SelfModule | PathRoot::Super(_) => {
            let levels = match path.root {
                PathRoot::Super(k) => k,
                _ => 0,
            };
            let target = ancestor(m, module, levels)
                .filter(|s| *s != NONE)
                .ok_or(Fail {
                    kind: DiagKind::SuperBeyondRoot { levels },
                    seg: 0,
                    near: Near::Nothing,
                })?;
            lookup_tables(
                m,
                w,
                target,
                ts,
                first.name,
                mode,
                all,
                0,
                Near::Lexical(target),
            )
            .unwrap_or_else(|| unresolved(first.name, None, 0, Near::Lexical(target)))
        }
        root => return Err(root_fail(root)),
    })
}

/// The witnesses of a ⊤ slot, as a slot for every table an import binds.
fn top_everywhere(m: &Model<'_>, a: u32, b: u32) -> Vec<(u8, Slot)> {
    tables(m, true)
        .into_iter()
        .map(|t| (t, Slot::Top(a, b)))
        .collect()
}

/// Tries to resolve import `i` against the current state. Pure: reads only.
fn attempt(m: &Model<'_>, w: &Work, i: u32, final_mode: bool) -> Attempt {
    let mode = Mode {
        final_mode,
        skip: i,
    };
    let fail0 = |kind| {
        Attempt::Fail(Fail {
            kind,
            seg: 0,
            near: Near::Nothing,
        })
    };
    let Some(imp) = m.imports.get(i as usize) else {
        return fail0(DiagKind::GlobsUnsupported);
    };
    let Some(unit) = m.units.get(imp.unit as usize) else {
        return fail0(DiagKind::GlobsUnsupported);
    };
    let hir = &unit.hir;
    let path = hir.path(imp.path);
    let segs = hir.list(path.segments);
    let n = segs.len();
    if path.qself.is_some() || path.root.is_type_root() || n == 0 {
        return fail0(DiagKind::RootUnsupported { root: path.root });
    }
    let from = imp.scope;
    let all_last = !imp.glob;
    let ts_for = |k: usize| tables(m, k + 1 == n && all_last);
    let mut deps: Vec<(u32, Name)> = Vec::new();
    let mut segs_out: Vec<(u32, Res, u32)> = Vec::new();
    let mut private: Option<(Name, Res, Vis, usize)> = None;
    let check_private = |slots: &[(u8, Slot)],
                         name: Name,
                         seg: usize,
                         private: &mut Option<(Name, Res, Vis, usize)>| {
        for (_, slot) in slots {
            let Slot::Hit(h) = slot else { continue };
            if private.is_some() {
                return;
            }
            if h.binding == NONE {
                if h.vis != Vis::Public && m.policy.visibility_enforced() {
                    *private = Some((name, h.res, h.vis, seg));
                }
            } else if let Some(b) = m.bindings.get(h.binding as usize) {
                if !m.accessible(b.vis, b.home, from) {
                    *private = Some((name, b.res, b.vis, seg));
                }
            }
        }
    };
    let first_ts = ts_for(0);
    let mut found = match first_step(m, w, i, mode, &first_ts, n == 1 && all_last) {
        Ok(Step::Found(f, dep)) => {
            deps.extend(dep);
            f
        }
        Ok(Step::Wait(s, name)) => return Attempt::Wait(s, name),
        Ok(Step::Fail(f)) | Err(f) => return Attempt::Fail(f),
    };
    let Some(first) = segs.first() else {
        return fail0(DiagKind::RootUnsupported { root: path.root });
    };
    let mut prev_name = first.name;
    if n == 1 && all_last {
        check_private(&found, prev_name, 0, &mut private);
    }
    for (k, seg) in segs.iter().enumerate().skip(1) {
        let container = match found.first() {
            Some(&(_, Slot::Hit(h))) => h,
            Some(&(_, Slot::Top(a, b))) => {
                // An ambiguous module path: the import is ⊤ in every table.
                if imp.glob {
                    return Attempt::Fail(ambiguous_fail(m, prev_name, a, b, k - 1));
                }
                return Attempt::Named {
                    slots: top_everywhere(m, a, b),
                    deps,
                    segs: segs_out,
                    private,
                };
            }
            None => break,
        };
        segs_out.push((ix(k - 1), container.res, container.binding));
        let ts = ts_for(k);
        let all = k + 1 == n && all_last;
        match step(m, w, container, prev_name, seg.name, &ts, mode, all, k) {
            Step::Found(f, dep) => {
                deps.extend(dep);
                if all {
                    check_private(&f, seg.name, k, &mut private);
                } else {
                    check_private(f.get(..1).unwrap_or(&[]), seg.name, k, &mut private);
                }
                found = f;
            }
            Step::Wait(s, name) => return Attempt::Wait(s, name),
            Step::Fail(f) => return Attempt::Fail(f),
        }
        prev_name = seg.name;
    }
    if imp.glob {
        let c = match found.first() {
            Some(&(_, Slot::Hit(h))) => h,
            Some(&(_, Slot::Top(a, b))) => {
                return Attempt::Fail(ambiguous_fail(m, prev_name, a, b, n - 1));
            }
            None => return fail0(DiagKind::GlobsUnsupported),
        };
        segs_out.push((ix(n - 1), c.res, c.binding));
        let container = if c.kind == DefKind::Module {
            m.scope_of(c.res).map(Container::Scope)
        } else {
            None
        }
        .or_else(|| m.sum_of(c.res).map(|_| Container::Sum))
        .or_else(|| {
            (m.is_outside(c.res)
                && matches!(c.kind, DefKind::Module | DefKind::Extern | DefKind::Sum))
            .then_some(Container::Outside(c.res))
        });
        return match container {
            Some(container) => Attempt::Glob {
                container,
                res: c.res,
                deps,
                segs: segs_out,
                private,
            },
            None => Attempt::Fail(Fail {
                kind: DiagKind::NotAContainer {
                    name: prev_name,
                    found: c.kind,
                },
                seg: n - 1,
                near: Near::Nothing,
            }),
        };
    }
    found.retain(|(_, s)| match s {
        Slot::Hit(h) => h.kind.fits(hir_lang::Ns::Import),
        Slot::Top(..) => true,
    });
    if found.is_empty() {
        return Attempt::Fail(Fail {
            kind: DiagKind::WrongKind {
                name: prev_name,
                ns: hir_lang::Ns::Import,
                found: DefKind::Prim,
            },
            seg: n - 1,
            near: Near::Nothing,
        });
    }
    if let Some(&(_, Slot::Hit(h))) = found.iter().find(|(_, s)| matches!(s, Slot::Hit(_))) {
        segs_out.push((ix(n - 1), h.res, h.binding));
    }
    Attempt::Named {
        slots: found,
        deps,
        segs: segs_out,
        private,
    }
}

fn ambiguous_fail(m: &Model<'_>, name: Name, a: u32, b: u32, seg: usize) -> Fail {
    let res = |x: u32| m.bindings.get(x as usize).map_or(Res::Err, |b| b.res);
    Fail {
        kind: DiagKind::AmbiguousGlob {
            name,
            first: res(a),
            second: res(b),
        },
        seg,
        near: Near::Nothing,
    }
}

// ------------------------------------------------------------- installing

fn import_hoist(m: &Model<'_>) -> Hoist {
    match m.policy.hoisting(ItemClass::Import) {
        Hoist::AfterDecl => Hoist::AfterDecl,
        Hoist::Scope | Hoist::Module => Hoist::Scope,
    }
}

fn import_span(m: &Model<'_>, i: u32) -> Span {
    m.imports
        .get(i as usize)
        .and_then(|imp| {
            m.units
                .get(imp.unit as usize)
                .map(|u| crate::collect::item_name_span(&u.hir, imp.item))
        })
        .unwrap_or(Span::empty(0))
}

/// A copy of binding `src` as import `i`'s binding of `name` in table `t`.
fn import_binding(m: &mut Model<'_>, i: u32, t: u8, name: Name, src: Hit) -> u32 {
    let (s, vis) = m
        .imports
        .get(i as usize)
        .map_or((NONE, Vis::Private), |imp| (imp.scope, imp.vis));
    let span = import_span(m, i);
    let hoist = import_hoist(m);
    m.push_binding(Binding {
        ns: t,
        name,
        res: src.res,
        kind: src.kind,
        vis,
        home: s,
        origin: Origin::Import(i),
        hoist,
        shadowed: false,
        span,
    })
}

/// A witness binding of a ⊤ slot, copied into import `i`.
fn witness(m: &mut Model<'_>, i: u32, t: u8, name: Name, b: u32) -> u32 {
    let hit = hit_of(m, b).unwrap_or(Hit {
        res: Res::Err,
        kind: DefKind::Err,
        vis: Vis::Private,
        binding: NONE,
    });
    import_binding(m, i, t, name, hit)
}

fn install_named(
    m: &mut Model<'_>,
    w: &mut Work,
    i: u32,
    slots: &[(u8, Slot)],
    segs: Vec<(u32, Res, u32)>,
    final_mode: bool,
) -> Result<(), ResolveError> {
    let first_res = slots.iter().find_map(|(_, s)| match s {
        Slot::Hit(h) => Some(h.res),
        Slot::Top(..) => None,
    });
    let Some(imp) = m.imports.get_mut(i as usize) else {
        return Ok(());
    };
    imp.state = ImportState::Done;
    imp.res = first_res.unwrap_or(Res::Err);
    imp.unresolved = 0;
    imp.late = final_mode;
    imp.segs = if first_res.is_some() {
        segs
    } else {
        Vec::new()
    };
    let _was = w.stuck.remove(&i);
    merge(m, w, i, slots, true)
}

/// Merges what import `i`'s path reaches now into its slots. Monotone: a
/// table not bound yet gets bound, a bound one can only turn ⊤. `first`
/// reports collisions (they are only new on the first merge).
fn merge(
    m: &mut Model<'_>,
    w: &mut Work,
    i: u32,
    slots: &[(u8, Slot)],
    first: bool,
) -> Result<(), ResolveError> {
    let Some(imp) = m.imports.get(i as usize) else {
        return Ok(());
    };
    let (s, unit, item, vis) = (imp.scope, imp.unit, imp.item, imp.vis);
    let Some(name) = imp.name else { return Ok(()) };
    let span = import_span(m, i);
    let mut changed = false;
    for &(t, slot) in slots {
        let key = (t, name);
        let current = w
            .named_res
            .get(s as usize)
            .and_then(|r| r.get(&key))
            .copied();
        let owner = |b: u32| m.bindings.get(b as usize).map(|x| x.origin);
        let mine = match current {
            Some(GState::One(b) | GState::Amb { a: b, .. }) => owner(b) == Some(Origin::Import(i)),
            None => true,
        };
        let def = def_in(m, w, s, key);
        if def.is_some() || !mine {
            if first {
                let prev = def.or(match current {
                    Some(GState::One(b) | GState::Amb { a: b, .. }) => Some(b),
                    None => None,
                });
                let at = prev
                    .and_then(|b| m.bindings.get(b as usize))
                    .map_or(Span::empty(0), |b| b.span);
                m.report(
                    unit,
                    DiagKind::Duplicate { name, first: at },
                    span,
                    Some(NodeRef::Item(item)),
                );
            }
            continue;
        }
        let next = match (current, slot) {
            (None, Slot::Hit(h)) => GState::One(import_binding(m, i, t, name, h)),
            (None, Slot::Top(a, b)) => GState::Amb {
                a: witness(m, i, t, name, a),
                b: witness(m, i, t, name, b),
                vis,
            },
            (Some(GState::One(x)), Slot::Top(_, b)) => GState::Amb {
                a: x,
                b: witness(m, i, t, name, b),
                vis,
            },
            (Some(GState::One(_)), Slot::Hit(_)) | (Some(GState::Amb { .. }), _) => continue,
        };
        if let Some(r) = w.named_res.get_mut(s as usize) {
            let _ = r.insert(key, next);
        }
        if let (Some(x), GState::Amb { .. }) = (w.top.get_mut(i as usize), next) {
            *x = true;
        }
        announce(w, s, next);
        changed = true;
    }
    if first || changed {
        wake(w, s, name);
    }
    if changed {
        // The path keeps a resolution while some table still has one
        // meaning; once every table is ⊤ it is an error (reported at the end).
        let any_one = (0..5u8).any(|t| {
            matches!(
                w.named_res.get(s as usize).and_then(|r| r.get(&(t, name))),
                Some(GState::One(b)) if m.bindings.get(*b as usize).map(|x| x.origin) == Some(Origin::Import(i))
            )
        });
        if !any_one {
            if let Some(imp) = m.imports.get_mut(i as usize) {
                imp.res = Res::Err;
                imp.segs.clear();
            }
        }
        wake_subs(w, s, name);
    }
    drain(m, w)
}

fn install_glob(
    m: &mut Model<'_>,
    w: &mut Work,
    i: u32,
    container: Container,
    res: Res,
    segs: Vec<(u32, Res, u32)>,
    final_mode: bool,
) -> Result<(), ResolveError> {
    let Some(imp) = m.imports.get_mut(i as usize) else {
        return Ok(());
    };
    imp.state = ImportState::Done;
    imp.res = res;
    imp.unresolved = 0;
    imp.late = final_mode;
    imp.segs = segs;
    let s = imp.scope;
    let _was = w.stuck.remove(&i);
    let span = import_span(m, i);
    let hoist = import_hoist(m);
    match container {
        Container::Scope(t) => {
            if let Some(list) = w.importers.get_mut(t as usize) {
                list.push((s, i));
            }
            let mut current: Vec<GState> = w
                .defs
                .get(t as usize)
                .map(|d| d.iter().map(|b| GState::One(*b)).collect())
                .unwrap_or_default();
            if let Some(r) = w.named_res.get(t as usize) {
                current.extend(r.values().copied());
            }
            if let Some(g) = w.glob_res.get(t as usize) {
                current.extend(g.values().copied());
            }
            for state in current {
                w.tasks.push_back(task_of(s, i, state));
            }
        }
        Container::Sum => {
            let Some((u, table)) = m.sum_of(res) else {
                return drain(m, w);
            };
            let variants = m.sums.get(table as usize).cloned().unwrap_or_default();
            for (sym, v) in variants {
                let unit_variant = m
                    .units
                    .get(u as usize)
                    .and_then(|unit| unit.hir.variant(v))
                    .is_some_and(|v| v.shape == hir_lang::Shape::Unit);
                let mut seen = [false; 5];
                for ns in [Namespace::Value, Namespace::Type] {
                    let t = m.policy.table_ix(ns);
                    match seen.get_mut(t as usize) {
                        Some(slot) if !*slot => *slot = true,
                        _ => continue,
                    }
                    let b = m.push_binding(Binding {
                        ns: t,
                        name: Name::new(sym),
                        res: Res::Def(m.def_id(u, Def::Variant(v))),
                        kind: DefKind::Variant { unit: unit_variant },
                        vis: Vis::Public,
                        home: s,
                        origin: Origin::Variant(i, v),
                        hoist,
                        shadowed: false,
                        span,
                    });
                    w.tasks.push_back(Task {
                        s,
                        g: i,
                        src: b,
                        top: false,
                    });
                }
            }
        }
        Container::Outside(c) => {
            for (name, ns, e) in env_members(m.env, c) {
                let t = m.policy.table_ix(ns);
                let b = m.push_binding(Binding {
                    ns: t,
                    name,
                    res: e.res,
                    kind: e.kind,
                    vis: e.vis,
                    home: s,
                    origin: Origin::Env,
                    hoist,
                    shadowed: false,
                    span,
                });
                w.tasks.push_back(Task {
                    s,
                    g: i,
                    src: b,
                    top: false,
                });
            }
        }
    }
    drain(m, w)
}

/// The propagation task carrying slot state `state` into scope `s` by glob `g`.
const fn task_of(s: u32, g: u32, state: GState) -> Task {
    match state {
        GState::One(b) => Task {
            s,
            g,
            src: b,
            top: false,
        },
        GState::Amb { a, .. } => Task {
            s,
            g,
            src: a,
            top: true,
        },
    }
}

/// Runs glob propagation tasks to completion.
fn drain(m: &mut Model<'_>, w: &mut Work) -> Result<(), ResolveError> {
    while let Some(task) = w.tasks.pop_front() {
        add_glob(m, w, task)?;
    }
    Ok(())
}

/// Slot state `state` changed in scope `s`: forward it to glob importers.
fn announce(w: &mut Work, s: u32, state: GState) {
    let Some(importers) = w.importers.get(s as usize) else {
        return;
    };
    // The forwarded state's visibility is read from the source scope when
    // the task runs (`slot_vis`), so a later widening is never missed.
    for &(s2, g2) in importers {
        w.tasks.push_back(task_of(s2, g2, state));
    }
}

/// The visibility a slot exports with: a binding's own, or a ⊤ slot's widest.
fn slot_vis(m: &Model<'_>, w: &Work, src: u32) -> Vis {
    let Some(b) = m.bindings.get(src as usize) else {
        return Vis::Private;
    };
    let key = (b.ns, b.name);
    let s = b.home as usize;
    let amb = |g: Option<&GState>| match g {
        Some(GState::Amb { a, vis, .. }) if *a == src => Some(*vis),
        _ => None,
    };
    amb(w.glob_res.get(s).and_then(|r| r.get(&key)))
        .or_else(|| amb(w.named_res.get(s).and_then(|r| r.get(&key))))
        .unwrap_or(b.vis)
}

/// Glob import `task.g` of scope `task.s` carries a slot into `task.s`.
fn add_glob(m: &mut Model<'_>, w: &mut Work, task: Task) -> Result<(), ResolveError> {
    let Task { s, g, src, top, .. } = task;
    let Some(&source) = m.bindings.get(src as usize) else {
        return Ok(());
    };
    // Bindings created for this scope directly (variants, environment
    // members) are already home here; others must be visible from here.
    let direct = source.home == s && matches!(source.origin, Origin::Variant(..) | Origin::Env);
    let src_vis = if direct {
        source.vis
    } else {
        slot_vis(m, w, src)
    };
    if !direct && !m.accessible(src_vis, source.home, s) {
        return Ok(());
    }
    let key = (source.ns, source.name);
    if def_in(m, w, s, key).is_some() || !named_of(w, s, source.name).is_empty() {
        return Ok(());
    }
    let gvis = m.imports.get(g as usize).map_or(Vis::Private, |i| i.vis);
    let c = min_vis(gvis, src_vis);
    let existing = w
        .glob_res
        .get(s as usize)
        .and_then(|r| r.get(&key))
        .copied();
    let fresh = |m: &mut Model<'_>| {
        if direct {
            src
        } else {
            m.push_binding(Binding {
                vis: c,
                home: s,
                origin: Origin::Glob(g, src),
                ..source
            })
        }
    };
    let wider = |a: Vis, b: Vis| if vis_rank(a) >= vis_rank(b) { a } else { b };
    let next = match existing {
        None if top => {
            let nb = fresh(m);
            GState::Amb {
                a: nb,
                b: nb,
                vis: c,
            }
        }
        None => GState::One(fresh(m)),
        Some(GState::One(x)) => {
            let Some(xb) = m.bindings.get(x as usize).copied() else {
                return Ok(());
            };
            if !top && xb.res == source.res {
                if vis_rank(c) <= vis_rank(xb.vis) {
                    return Ok(());
                }
                // The same meaning through a more visible route.
                GState::One(fresh(m))
            } else {
                GState::Amb {
                    a: x,
                    b: fresh(m),
                    vis: wider(xb.vis, c),
                }
            }
        }
        Some(GState::Amb { a, b, vis }) => {
            if vis_rank(c) <= vis_rank(vis) {
                return Ok(());
            }
            GState::Amb { a, b, vis: c }
        }
    };
    if w.budget == 0 {
        return Err(ResolveError::BudgetExceeded {
            limit: Limit::GlobBindings,
        });
    }
    w.budget -= 1;
    if let Some(r) = w.glob_res.get_mut(s as usize) {
        let _ = r.insert(key, next);
    }
    wake(w, s, source.name);
    wake_subs(w, s, source.name);
    announce(w, s, next);
    Ok(())
}

// ------------------------------------------------------------- finishing

/// Named imports that ended ⊤ are reported once, at the import.
fn report_top(m: &mut Model<'_>, w: &Work) {
    for i in 0..m.imports.len() {
        let Some(imp) = m.imports.get(i) else {
            continue;
        };
        if imp.glob || !w.top.get(i).copied().unwrap_or(false) {
            continue;
        }
        let Some(name) = imp.name else { continue };
        let witnesses = w
            .named_res
            .get(imp.scope as usize)
            .into_iter()
            .flat_map(|r| r.iter())
            .find_map(|((_, n), g)| match g {
                GState::Amb { a, b, .. } if *n == name => Some((*a, *b)),
                _ => None,
            });
        let res = |x: u32| m.bindings.get(x as usize).map_or(Res::Err, |b| b.res);
        let (first, second) = witnesses.map_or((Res::Err, Res::Err), |(a, b)| (res(a), res(b)));
        if let Some((unit, span, path)) = seg_site(m, ix(i), usize::MAX) {
            m.report(
                unit,
                DiagKind::AmbiguousGlob {
                    name,
                    first,
                    second,
                },
                span,
                Some(NodeRef::Path(path)),
            );
        }
    }
}

/// Imports settled in final mode are checked again now that every table is
/// final; one that would resolve differently is ambiguous.
fn recheck_late(m: &mut Model<'_>, w: &Work) {
    let late: Vec<u32> = m
        .imports
        .iter()
        .enumerate()
        .filter(|(i, imp)| {
            imp.late && imp.state == ImportState::Done && !w.top.get(*i).copied().unwrap_or(false)
        })
        .map(|(i, _)| ix(i))
        .collect();
    for i in late {
        let now = match attempt(m, w, i, true) {
            Attempt::Named { slots, .. } => slots.iter().find_map(|(_, s)| match s {
                Slot::Hit(h) => Some(h.res),
                Slot::Top(..) => None,
            }),
            Attempt::Glob { res, .. } => Some(res),
            _ => None,
        };
        let Some(imp) = m.imports.get(i as usize) else {
            continue;
        };
        if now != Some(imp.res) {
            let hir = m.units.get(imp.unit as usize).map(|u| &u.hir);
            let last = hir.and_then(|h| h.list(h.path(imp.path).segments).last().map(|s| s.name));
            let Some(name) = imp.name.or(last) else {
                continue;
            };
            if let Some((unit, span, path)) = seg_site(m, i, usize::MAX) {
                m.report(
                    unit,
                    DiagKind::ImportAmbiguity { name },
                    span,
                    Some(NodeRef::Path(path)),
                );
            }
        }
    }
}

const fn entry_state(g: GState) -> EntryState {
    match g {
        GState::One(b) => EntryState::One(b),
        GState::Amb { a, b, .. } => EntryState::Ambiguous(a, b),
    }
}

/// Builds every scope's final sorted table.
fn build_tables(m: &mut Model<'_>, w: &Work) {
    for s in 0..m.scopes.len() {
        let mut table: Vec<Entry> = Vec::new();
        if let Some(scope) = m.scopes.get(s) {
            for &b in &scope.defs {
                if let Some(binding) = m.bindings.get(b as usize).filter(|b| !b.shadowed) {
                    table.push(Entry {
                        ns: binding.ns,
                        name: binding.name,
                        state: EntryState::One(b),
                    });
                }
            }
            for &i in &scope.named {
                let Some(imp) = m.imports.get(i as usize) else {
                    continue;
                };
                if imp.state == ImportState::Failed {
                    if let Some(name) = imp.name {
                        table.push(Entry {
                            ns: ANY_NS,
                            name,
                            state: EntryState::Failed(i),
                        });
                    }
                }
            }
        }
        for map in [w.named_res.get(s), w.glob_res.get(s)]
            .into_iter()
            .flatten()
        {
            for (&(ns, name), &g) in map {
                table.push(Entry {
                    ns,
                    name,
                    state: entry_state(g),
                });
            }
        }
        table.sort_by(entry_order);
        // Several failed imports of one name: one entry is enough.
        table.dedup_by(|a, b| a.ns == ANY_NS && b.ns == ANY_NS && a.name == b.name);
        if let Some(scope) = m.scopes.get_mut(s) {
            scope.table = table;
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use alloc::vec::Vec;

    use hir_lang::{FnDef, Item, ItemId, ItemKind, Name, Ns, Path, PathRoot, Segment, Vis};

    use crate::{
        diag::DiagKind,
        model::{EntryState, ImportState, Model, fixture::*},
        policy::Policy,
    };

    fn public_fn(f: &mut Fixture, name: Name) -> ItemId {
        let body = f.b.block(&[], None);
        f.b.item(
            Item::new(
                Some(name),
                ItemKind::Fn(FnDef {
                    body: Some(body),
                    ..FnDef::default()
                }),
            )
            .with_vis(Vis::Public),
        )
    }

    fn import(f: &mut Fixture, parts: &[Name], alias: Option<Name>, glob: bool) -> ItemId {
        let segs: Vec<Segment> = parts
            .iter()
            .map(|n| Segment::new(*n, f.b.origin()))
            .collect();
        let segs = f.b.list(&segs);
        let path = f.b.path(Path {
            root: PathRoot::Super(1),
            ..Path::new(segs, Ns::Import)
        });
        f.b.item(Item::new(alias, ItemKind::Import { path, glob }).with_vis(Vis::Public))
    }

    /// mod a { pub fn x }  mod b { pub fn x }  mod c { pub use super::a::x; }
    /// mod d { use super::a::*; use super::c::*; }   (same meaning twice)
    /// mod e { use super::a::*; use super::b::*; }   (two meanings)
    fn globs() -> (Model<'static>, [u32; 2], Name) {
        let mut f = Fixture::new();
        let (x, a, b, c, d, e) = (
            f.name("x"),
            f.name("a"),
            f.name("b"),
            f.name("c"),
            f.name("d"),
            f.name("e"),
        );
        let ax = public_fn(&mut f, x);
        let ma = f.b.module(Some(a), &[ax]);
        let bx = public_fn(&mut f, x);
        let mb = f.b.module(Some(b), &[bx]);
        let cx = import(&mut f, &[a, x], None, false);
        let mc = f.b.module(Some(c), &[cx]);
        let d1 = import(&mut f, &[a], None, true);
        let d2 = import(&mut f, &[c], None, true);
        let md = f.b.module(Some(d), &[d1, d2]);
        let e1 = import(&mut f, &[a], None, true);
        let e2 = import(&mut f, &[b], None, true);
        let me = f.b.module(Some(e), &[e1, e2]);
        let root = f.b.module(None, &[ma, mb, mc, md, me]);
        let hir = f.finish(root);
        let m = model(hir, &f.names, Policy::new());
        let s = [scope(&m, md), scope(&m, me)];
        (m, s, x)
    }

    #[test]
    fn test_glob_join_same_meaning_is_one_binding() {
        let (m, [d, _], x) = globs();
        assert!(matches!(m.find(d, 0, x), Some(EntryState::One(_))));
    }

    #[test]
    fn test_glob_join_two_meanings_is_ambiguous() {
        let (m, [_, e], x) = globs();
        assert!(matches!(m.find(e, 0, x), Some(EntryState::Ambiguous(..))));
        assert!(m.diags.is_empty(), "ambiguity is reported at use sites");
    }

    #[test]
    fn test_named_import_through_ambiguity_becomes_ambiguous() {
        // ... mod e { use a::*; use b::*; }  mod g { pub use super::e::x as y; }
        let mut f = Fixture::new();
        let (x, y, a, b, e, g) = (
            f.name("x"),
            f.name("y"),
            f.name("a"),
            f.name("b"),
            f.name("e"),
            f.name("g"),
        );
        let ax = public_fn(&mut f, x);
        let ma = f.b.module(Some(a), &[ax]);
        let bx = public_fn(&mut f, x);
        let mb = f.b.module(Some(b), &[bx]);
        let e1 = import(&mut f, &[a], None, true);
        let e2 = import(&mut f, &[b], None, true);
        let me = f.b.module(Some(e), &[e1, e2]);
        let gy = import(&mut f, &[e, x], Some(y), false);
        let mg = f.b.module(Some(g), &[gy]);
        let root = f.b.module(None, &[ma, mb, me, mg]);
        let hir = f.finish(root);
        let m = model(hir, &f.names, Policy::new());
        let s = scope(&m, mg);
        assert!(matches!(m.find(s, 0, y), Some(EntryState::Ambiguous(..))));
        let imp = m.imports.iter().find(|i| i.name == Some(y)).unwrap();
        assert_eq!(imp.state, ImportState::Done);
        assert_eq!(imp.res, hir_lang::Res::Err);
        assert_eq!(m.diags.len(), 1);
        assert!(matches!(m.diags[0].kind, DiagKind::AmbiguousGlob { .. }));
    }

    #[test]
    fn test_import_does_not_resolve_through_itself() {
        // use os;  with nothing named os anywhere: unresolved, not a cycle.
        let mut f = Fixture::new();
        let os = f.name("os");
        let segs = [Segment::new(os, f.b.origin())];
        let segs = f.b.list(&segs);
        let path = f.b.path(Path::new(segs, Ns::Import));
        let imp =
            f.b.item(Item::new(None, ItemKind::Import { path, glob: false }));
        let root = f.b.module(None, &[imp]);
        let hir = f.finish(root);
        let m = model(hir, &f.names, Policy::new());
        assert_eq!(m.imports[0].state, ImportState::Failed);
        assert!(matches!(m.diags[0].kind, DiagKind::Unresolved { .. }));
    }
}
