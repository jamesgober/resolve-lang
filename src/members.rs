//! Phase 4: class member tables, mixin expansion, and the paths that need
//! them (`self::x`, `parent::x`, `static::x`, `Class::member`).
//!
//! HIR leaves mixin uses (PHP `use T { m insteadof U; m as protected n; }`)
//! for resolve-lang to expand after resolution. Expansion builds each class's
//! *effective* member table: its own members, then every mixin member not
//! excluded by an `insteadof` rule and not already defined by the class, plus
//! the aliases the rules add. Mixins that use mixins are expanded first, in
//! dependency order; a cycle is reported and broken.
//!
//! Inherited lookups follow the C3 method resolution order (Python's, and
//! Dylan's before it). A class with exactly one base `B` has the order
//! `C, L(B)`, so lookups walk single-base chains directly and memoize the
//! answer for the whole chain (a long single-inheritance chain costs O(1)
//! amortized per distinct name). A class with several bases gets its
//! linearization computed once, eagerly, in dependency order (iteratively):
//! `C` followed by the merge of its bases' linearizations and the base list,
//! taking at each step the first head that is in no list's tail. When no head
//! qualifies the hierarchy is inconsistent; that is reported (as Python's
//! `TypeError` at class creation) and the class falls back to its bases'
//! linearizations concatenated left to right without repeats, so lookups
//! still answer. Outside classes (from the environment) are leaves: the
//! environment answers for their own ancestors. A base that is still being
//! linearized (an inheritance cycle) is treated as a leaf, so every class
//! gets an order. Every step is charged to the [`Budget`](crate::Budget).
//!
//! Member tables are keyed like every other table (`Fold::key`), so under a
//! case-insensitive value table `self::FOO()` finds method `foo`, while class
//! constants stay case-sensitive.

use alloc::{collections::BTreeMap, vec::Vec};

use hir_lang::{
    DefId, ItemId, ItemKind, MixinAction, Name, NodeRef, PathId, PathRoot, Res, Span, Symbol, Ty,
    TyId, Vis,
};

use crate::{
    diag::DiagKind,
    env::{DefKind, env_members},
    error::{Limit, ResolveError},
    imports::Hit,
    model::{Binding, Model, NONE, Origin, ScopeKind, ix},
    pass::{DeferKind, Deferred, SegRef, TypeCtx, UnitOut, tables_for},
    policy::{Hoist, Namespace, RootBinding},
};

/// One member of a class's effective table.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Member {
    pub(crate) ns: u8,
    pub(crate) name: Name,
    pub(crate) binding: u32,
    /// The mixin it came from, or `None` for an own member.
    pub(crate) from: Option<Res>,
}

/// A member found by lookup.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Found {
    pub(crate) hit: Hit,
    /// The class scope whose table holds it (`NONE` for an outside class).
    pub(crate) owner: u32,
}

pub(crate) struct Members {
    /// Effective member tables by scope index (empty for non-classes), sorted
    /// by (table, key).
    pub(crate) tables: Vec<Vec<Member>>,
    /// Resolved bases by scope index.
    pub(crate) bases: Vec<Vec<Res>>,
    /// By scope index, for classes with several bases: the C3 linearization
    /// without the class itself.
    mro: Vec<Option<Vec<Res>>>,
    memo: BTreeMap<(u32, u8, Name), Option<Found>>,
    stamp: Vec<u32>,
    epoch: u32,
    steps: u64,
}

/// The resolution a path got in phase 3 (or carried in): fully resolved
/// paths only.
pub(crate) fn path_res(m: &Model<'_>, outs: &[UnitOut], u: u32, p: PathId) -> Option<Res> {
    let unit = m.units.get(u as usize)?;
    let planned = outs.get(u as usize)?.plan.get(p.index()).copied().flatten();
    match planned {
        Some((res, 0)) => Some(res),
        Some(_) => None,
        None => {
            let path = unit.hir.get_path(p)?;
            (path.unresolved == 0 && !path.res.is_unresolved()).then_some(path.res)
        }
    }
}

/// An ordered key for a resolution (`Res` itself is not `Ord`).
type ResKey = (u8, Option<DefId>, u32);

fn res_key(r: Res) -> ResKey {
    match r {
        Res::Def(d) => (0, Some(d), 0),
        Res::Extern(s) => (1, None, s.as_u32()),
        Res::Local(b) => (2, None, b.index() as u32),
        Res::Prim(p) => (3, None, p as u32),
        Res::Unresolved => (4, None, 0),
        Res::Err => (5, None, 0),
    }
}

/// The member a mixin rule names (as written): compared by each member's
/// table key, so PHP's case-insensitive method names match in any case.
fn rule_member(
    fold: &crate::model::Fold,
    sources: &[Source],
    from: Option<Res>,
    sym: Symbol,
) -> Option<(Res, (u8, Name, u32))> {
    sources
        .iter()
        .filter(|(r, _)| from.is_none_or(|f| f == *r))
        .flat_map(|(r, list)| list.iter().map(move |x| (*r, *x)))
        .find(|(_, (t, key, _))| key.mark.is_root() && fold.key(*t, Name::new(sym)).sym == key.sym)
}

/// The resolution of a type term that is a path.
pub(crate) fn ty_res(m: &Model<'_>, outs: &[UnitOut], u: u32, ty: TyId) -> Option<Res> {
    let unit = m.units.get(u as usize)?;
    let Ty::Path(p) = *unit.hir.get_ty(ty)? else {
        return None;
    };
    path_res(m, outs, u, p)
}

fn ty_span(m: &Model<'_>, u: u32, t: TyId) -> Span {
    m.units
        .get(u as usize)
        .map_or(Span::empty(0), |x| x.hir.origin(NodeRef::Ty(t)).span)
}

/// A mixin-use item and its mixins with their resolutions.
type MixinUse = (ItemId, Vec<(TyId, Res)>);

/// An `as` rule: the mixin, the member (table, name, binding), the new name,
/// the new visibility.
type AliasRule = (Res, (u8, Name, u32), Option<hir_lang::Ident>, Option<Vis>);

/// A mixin's members as (table, name, binding).
type Source = (Res, Vec<(u8, Name, u32)>);

impl Members {
    /// Builds every class's base list, effective member table, and (for
    /// classes with several bases) C3 linearization.
    pub(crate) fn build(
        m: &mut Model<'_>,
        outs: &[UnitOut],
        steps: u64,
    ) -> Result<Self, ResolveError> {
        let n = m.scopes.len();
        let mut me = Self {
            tables: (0..n).map(|_| Vec::new()).collect(),
            bases: (0..n).map(|_| Vec::new()).collect(),
            mro: (0..n).map(|_| None).collect(),
            memo: BTreeMap::new(),
            stamp: alloc::vec![0; n],
            epoch: 0,
            steps,
        };
        for s in 0..n {
            let Some(scope) = m.scopes.get(s) else {
                continue;
            };
            let ScopeKind::Type(item, _) = scope.kind else {
                continue;
            };
            let u = scope.unit;
            if let Some(unit) = m.units.get(u as usize) {
                let tys: &[TyId] = match &unit.hir.item(item).kind {
                    ItemKind::Class(c) => unit.hir.list(c.bases),
                    ItemKind::Interface(i) => unit.hir.list(i.supers),
                    _ => &[],
                };
                let bases: Vec<Res> = tys
                    .iter()
                    .map(|t| ty_res(m, outs, u, *t).unwrap_or(Res::Err))
                    .collect();
                if let Some(slot) = me.bases.get_mut(s) {
                    *slot = bases;
                }
            }
            let mut own: Vec<Member> = scope
                .defs
                .iter()
                .filter_map(|b| {
                    let x = m.bindings.get(*b as usize)?;
                    (!x.shadowed).then_some(Member {
                        ns: x.ns,
                        name: x.key,
                        binding: *b,
                        from: None,
                    })
                })
                .collect();
            own.sort_by_key(|x| (x.ns, x.name));
            if let Some(slot) = me.tables.get_mut(s) {
                *slot = own;
            }
        }
        me.expand_mixins(m, outs);
        me.linearize_all(m)?;
        Ok(me)
    }

    /// The resolution naming class scope `s`.
    fn class_res(m: &Model<'_>, s: u32) -> Option<Res> {
        let scope = m.scopes.get(s as usize)?;
        let ScopeKind::Type(item, _) = scope.kind else {
            return None;
        };
        let unit = m.units.get(scope.unit as usize)?;
        Some(Res::Def(hir_lang::DefId::foreign(
            unit.id,
            hir_lang::Def::Item(item),
        )))
    }

    /// Whether `res` is a usable base (a class or interface, program or
    /// outside; not an error).
    fn usable_base(res: Res) -> bool {
        !matches!(res, Res::Err | Res::Unresolved)
    }

    /// The linearization of base `b` including itself: `b`, then its own
    /// order. Single-base chains are walked; a class with several bases
    /// contributes its stored order; `None` in `mro` for such a class means
    /// it is still being linearized (a cycle), so it is a leaf here.
    fn full_order(&mut self, m: &Model<'_>, b: Res) -> Result<Vec<Res>, ResolveError> {
        let mut out = alloc::vec![b];
        let mut cur = b;
        self.epoch = self.epoch.wrapping_add(1).max(1);
        let epoch = self.epoch;
        loop {
            self.charge()?;
            let Some(s) = m.scope_of(cur) else { break };
            match self.stamp.get_mut(s as usize) {
                Some(st) if *st == epoch => break,
                Some(st) => *st = epoch,
                None => break,
            }
            let bases: Vec<Res> = self
                .bases
                .get(s as usize)
                .map(|v| {
                    v.iter()
                        .copied()
                        .filter(|r| Self::usable_base(*r))
                        .collect()
                })
                .unwrap_or_default();
            match bases.as_slice() {
                [] => break,
                [one] => {
                    if out.contains(one) {
                        break;
                    }
                    out.push(*one);
                    cur = *one;
                }
                _ => {
                    let order = self.mro.get(s as usize).cloned().flatten();
                    for r in order.unwrap_or_default() {
                        self.charge()?;
                        if !out.contains(&r) {
                            out.push(r);
                        }
                    }
                    break;
                }
            }
        }
        Ok(out)
    }

    /// Computes the C3 linearization of every class with several bases,
    /// bases first, without recursion; reports inconsistent hierarchies.
    fn linearize_all(&mut self, m: &mut Model<'_>) -> Result<(), ResolveError> {
        let n = m.scopes.len();
        // 0 = not started, 1 = in progress, 2 = done.
        let mut state = alloc::vec![0u8; n];
        let multi = |me: &Self, s: usize| {
            me.bases
                .get(s)
                .is_some_and(|b| b.iter().filter(|r| Self::usable_base(**r)).count() > 1)
        };
        for root in 0..n {
            if !multi(self, root) || state.get(root) != Some(&0) {
                continue;
            }
            let mut stack: Vec<u32> = alloc::vec![ix(root)];
            if let Some(st) = state.get_mut(root) {
                *st = 1;
            }
            while let Some(&s) = stack.last() {
                // The first multi-base class this one depends on (through
                // single-base chains) that is not linearized yet.
                let mut dep = None;
                let bases: Vec<Res> = self.bases.get(s as usize).cloned().unwrap_or_default();
                'bases: for b in bases {
                    let mut cur = b;
                    let mut guard = 0usize;
                    while let Some(t) = m.scope_of(cur) {
                        self.charge()?;
                        guard += 1;
                        if guard > n {
                            break;
                        }
                        if multi(self, t as usize) {
                            if state.get(t as usize) == Some(&0) {
                                dep = Some(t);
                                break 'bases;
                            }
                            break;
                        }
                        match self.bases.get(t as usize).map(Vec::as_slice) {
                            Some([one]) => cur = *one,
                            _ => break,
                        }
                    }
                }
                if let Some(t) = dep {
                    if let Some(st) = state.get_mut(t as usize) {
                        *st = 1;
                    }
                    stack.push(t);
                    continue;
                }
                let _ = stack.pop();
                self.linearize_one(m, s)?;
                if let Some(st) = state.get_mut(s as usize) {
                    *st = 2;
                }
            }
        }
        Ok(())
    }

    /// C3 for one class whose bases' orders are known (or are leaves).
    fn linearize_one(&mut self, m: &mut Model<'_>, s: u32) -> Result<(), ResolveError> {
        let bases: Vec<Res> = self
            .bases
            .get(s as usize)
            .map(|v| {
                v.iter()
                    .copied()
                    .filter(|r| Self::usable_base(*r))
                    .collect()
            })
            .unwrap_or_default();
        let mut lists: Vec<Vec<Res>> = Vec::with_capacity(bases.len() + 1);
        for &b in &bases {
            lists.push(self.full_order(m, b)?);
        }
        lists.push(bases.clone());
        // How often each class still occurs in some list's tail (past its
        // head), so a head is checked in O(log n) instead of rescanning.
        let mut heads: Vec<usize> = alloc::vec![0; lists.len()];
        let mut in_tail: BTreeMap<ResKey, u32> = BTreeMap::new();
        for l in &lists {
            for r in l.iter().skip(1) {
                self.charge()?;
                *in_tail.entry(res_key(*r)).or_insert(0) += 1;
            }
        }
        let mut order: Vec<Res> = Vec::new();
        let consistent = loop {
            let mut pick = None;
            let mut any = false;
            for (li, l) in lists.iter().enumerate() {
                self.charge()?;
                let Some(&h) = heads.get(li).and_then(|&k| l.get(k)) else {
                    continue;
                };
                any = true;
                if in_tail.get(&res_key(h)).copied().unwrap_or(0) == 0 {
                    pick = Some(h);
                    break;
                }
            }
            if !any {
                break true;
            }
            let Some(h) = pick else { break false };
            order.push(h);
            for (li, l) in lists.iter().enumerate() {
                let Some(k) = heads.get_mut(li) else { continue };
                if l.get(*k) == Some(&h) {
                    *k += 1;
                    // The new head leaves the tail.
                    if let Some(&nh) = l.get(*k) {
                        if let Some(c) = in_tail.get_mut(&res_key(nh)) {
                            *c = c.saturating_sub(1);
                        }
                    }
                }
            }
        };
        if !consistent {
            order.clear();
            for l in lists.iter().take(bases.len()) {
                for r in l {
                    self.charge()?;
                    if !order.contains(r) {
                        order.push(*r);
                    }
                }
            }
            if let Some(scope) = m.scopes.get(s as usize) {
                if let ScopeKind::Type(item, _) = scope.kind {
                    let u = scope.unit;
                    if let Some(unit) = m.units.get(u as usize) {
                        let span = crate::collect::item_name_span(&unit.hir, item);
                        if let Some(name) = unit.hir.item(item).name {
                            m.report(
                                u,
                                DiagKind::InconsistentMro { class: name },
                                span,
                                Some(NodeRef::Item(item)),
                            );
                        }
                    }
                }
            }
        }
        let me = Self::class_res(m, s);
        order.retain(|r| Some(*r) != me);
        if let Some(slot) = self.mro.get_mut(s as usize) {
            *slot = Some(order);
        }
        Ok(())
    }

    /// Expands mixin uses, mixins before the classes that use them.
    fn expand_mixins(&mut self, m: &mut Model<'_>, outs: &[UnitOut]) {
        let n = m.scopes.len();
        // Per class: (use item, [(mixin type, its resolution)]).
        let mut uses: Vec<Vec<MixinUse>> = (0..n).map(|_| Vec::new()).collect();
        for (s, slot) in uses.iter_mut().enumerate() {
            let Some(scope) = m.scopes.get(s) else {
                continue;
            };
            let u = scope.unit;
            let Some(unit) = m.units.get(u as usize) else {
                continue;
            };
            for &use_item in &scope.mixin_uses {
                let ItemKind::MixinUse(def) = unit.hir.item(use_item).kind else {
                    continue;
                };
                let tys: Vec<(TyId, Res)> = unit
                    .hir
                    .list(def.mixins)
                    .iter()
                    .map(|t| (*t, ty_res(m, outs, u, *t).unwrap_or(Res::Err)))
                    .collect();
                slot.push((use_item, tys));
            }
        }
        // Iterative post-order DFS over "uses mixin" edges.
        let mut state = alloc::vec![0u8; n];
        let mut order: Vec<u32> = Vec::new();
        let mut cyclic: Vec<(u32, ItemId, TyId)> = Vec::new();
        for root in 0..n {
            if uses.get(root).is_none_or(Vec::is_empty) || state.get(root) != Some(&0) {
                continue;
            }
            if let Some(st) = state.get_mut(root) {
                *st = 1;
            }
            let mut stack: Vec<(u32, usize, usize)> = alloc::vec![(ix(root), 0, 0)];
            while let Some(top) = stack.last_mut() {
                let (s, ui, ti) = *top;
                let list = uses.get(s as usize).map_or(&[][..], Vec::as_slice);
                let Some((use_item, tys)) = list.get(ui) else {
                    let _ = stack.pop();
                    if let Some(st) = state.get_mut(s as usize) {
                        *st = 2;
                    }
                    order.push(s);
                    continue;
                };
                let Some(&(ty, res)) = tys.get(ti) else {
                    top.1 += 1;
                    top.2 = 0;
                    continue;
                };
                top.2 += 1;
                let Some(dep) = m.scope_of(res) else { continue };
                match state.get(dep as usize).copied() {
                    Some(0) => {
                        if let Some(st) = state.get_mut(dep as usize) {
                            *st = 1;
                        }
                        stack.push((dep, 0, 0));
                    }
                    Some(1) => cyclic.push((s, *use_item, ty)),
                    _ => {}
                }
            }
        }
        for &(s, use_item, ty) in &cyclic {
            let u = m.scopes.get(s as usize).map_or(0, |x| x.unit);
            let span = ty_span(m, u, ty);
            m.report(u, DiagKind::MixinCycle, span, Some(NodeRef::Item(use_item)));
        }
        for s in order {
            let list = uses
                .get_mut(s as usize)
                .map(core::mem::take)
                .unwrap_or_default();
            for (use_item, tys) in list {
                let tys: Vec<(TyId, Res)> = tys
                    .into_iter()
                    .filter(|(t, _)| {
                        !cyclic
                            .iter()
                            .any(|(cs, cu, ct)| *cs == s && *cu == use_item && ct == t)
                    })
                    .collect();
                self.expand_one(m, outs, s, use_item, &tys);
            }
        }
    }

    /// The members a mixin contributes, or `None` (reported) if it is not one.
    fn source(&self, m: &mut Model<'_>, s: u32, u: u32, ty: TyId, res: Res) -> Option<Source> {
        if matches!(res, Res::Err | Res::Unresolved) {
            return None;
        }
        if let Some(t) = m.scope_of(res) {
            let kind = match res {
                Res::Def(d) => m.kind_of_def(d),
                _ => None,
            };
            if kind != Some(DefKind::Class { mixin: true }) {
                let span = ty_span(m, u, ty);
                let found = kind.unwrap_or(DefKind::Err);
                m.report(
                    u,
                    DiagKind::NotAMixin { found },
                    span,
                    Some(NodeRef::Ty(ty)),
                );
                return None;
            }
            let members = self
                .tables
                .get(t as usize)
                .map(|v| v.iter().map(|x| (x.ns, x.name, x.binding)).collect())
                .unwrap_or_default();
            return Some((res, members));
        }
        if m.is_outside(res) {
            let mut members = Vec::new();
            for (name, ns, e) in env_members(m.env, res) {
                let t = m.policy.table_ix(ns);
                let key = m.fold.key(t, name);
                let b = m.push_binding(Binding {
                    ns: t,
                    name,
                    key,
                    res: e.res,
                    kind: e.kind,
                    vis: e.vis,
                    home: s,
                    origin: Origin::Env,
                    hoist: Hoist::Scope,
                    shadowed: false,
                    span: Span::empty(0),
                });
                members.push((t, key, b));
            }
            return Some((res, members));
        }
        let span = ty_span(m, u, ty);
        let found = match res {
            Res::Prim(_) => DefKind::Prim,
            Res::Local(_) => DefKind::Local,
            Res::Def(d) => m.kind_of_def(d).unwrap_or(DefKind::Err),
            _ => DefKind::Err,
        };
        m.report(
            u,
            DiagKind::NotAMixin { found },
            span,
            Some(NodeRef::Ty(ty)),
        );
        None
    }

    /// Applies one mixin use to class scope `s`.
    fn expand_one(
        &mut self,
        m: &mut Model<'_>,
        outs: &[UnitOut],
        s: u32,
        use_item: ItemId,
        tys: &[(TyId, Res)],
    ) {
        let Some(u) = m.scopes.get(s as usize).map(|x| x.unit) else {
            return;
        };
        let Some((rules, use_span)) = m.units.get(u as usize).and_then(|unit| {
            let ItemKind::MixinUse(def) = unit.hir.item(use_item).kind else {
                return None;
            };
            Some((
                unit.hir.list(def.rules).to_vec(),
                unit.hir.origin(NodeRef::Item(use_item)).span,
            ))
        }) else {
            return;
        };
        let mut sources: Vec<Source> = Vec::new();
        for &(ty, res) in tys {
            if let Some(src) = self.source(m, s, u, ty, res) {
                sources.push(src);
            }
        }
        let mut excluded: Vec<(Res, Symbol)> = Vec::new();
        let mut aliases: Vec<AliasRule> = Vec::new();
        for rule in &rules {
            let from = rule.from.and_then(|t| ty_res(m, outs, u, t));
            let Some(found) = rule_member(&m.fold, &sources, from, rule.method.sym) else {
                let span = if rule.method.span == Span::empty(0) {
                    use_span
                } else {
                    rule.method.span
                };
                m.report(
                    u,
                    DiagKind::UnknownMixinMember {
                        name: rule.method.sym,
                    },
                    span,
                    Some(NodeRef::Item(use_item)),
                );
                continue;
            };
            match rule.action {
                MixinAction::Insteadof(others) => {
                    let others: Vec<TyId> = m
                        .units
                        .get(u as usize)
                        .map(|x| x.hir.list(others).to_vec())
                        .unwrap_or_default();
                    for t in others {
                        if let Some(r) = ty_res(m, outs, u, t) {
                            excluded.push((r, rule.method.sym));
                        }
                    }
                }
                MixinAction::Alias { name, vis } => aliases.push((found.0, found.1, name, vis)),
            }
        }
        let own: Vec<(u8, Name)> = self
            .tables
            .get(s as usize)
            .map(|v| v.iter().map(|x| (x.ns, x.name)).collect())
            .unwrap_or_default();
        let is_own = |key: (u8, Name)| own.binary_search(&key).is_ok();
        // Mixin members, first mixin first; a second one with another
        // meaning and no `insteadof` is a conflict.
        let mut added: Vec<(u8, Name, u32, Res)> = Vec::new();
        let mut conflicts: Vec<(Name, hir_lang::DefId, hir_lang::DefId)> = Vec::new();
        for (res, list) in &sources {
            for &(ns, name, b) in list {
                if excluded
                    .iter()
                    .any(|(r, sym)| r == res && m.fold.key(ns, Name::new(*sym)).sym == name.sym)
                    || is_own((ns, name))
                {
                    continue;
                }
                if let Some(&(_, _, first, _)) = added.iter().find(|x| x.0 == ns && x.1 == name) {
                    let fr = m.bindings.get(first as usize).map(|x| x.res);
                    let sr = m.bindings.get(b as usize).map(|x| x.res);
                    if let (Some(Res::Def(fd)), Some(Res::Def(sd))) = (fr, sr) {
                        if fd != sd {
                            let spelled = m.bindings.get(b as usize).map_or(name, |x| x.name);
                            conflicts.push((spelled, fd, sd));
                        }
                    }
                    continue;
                }
                added.push((ns, name, b, *res));
            }
        }
        conflicts.dedup_by_key(|c| c.0);
        for (name, first, second) in conflicts {
            m.report(
                u,
                DiagKind::MixinConflict {
                    name,
                    first,
                    second,
                },
                use_span,
                Some(NodeRef::Item(use_item)),
            );
        }
        let mut new_members: Vec<Member> = added
            .iter()
            .map(|&(ns, name, binding, r)| Member {
                ns,
                name,
                binding,
                from: Some(r),
            })
            .collect();
        for (r, (ns, name, b), alias, vis) in aliases {
            let Some(orig) = m.bindings.get(b as usize).copied() else {
                continue;
            };
            let new_name = alias.map_or(orig.name, |a| Name::new(a.sym));
            let new_key = alias.map_or(name, |a| m.fold.key(ns, Name::new(a.sym)));
            if is_own((ns, new_key)) {
                continue;
            }
            let nb = m.push_binding(Binding {
                name: new_name,
                key: new_key,
                vis: vis.unwrap_or(orig.vis),
                home: s,
                origin: Origin::Mixin(b),
                span: alias.map_or(orig.span, |a| a.span),
                ..orig
            });
            new_members.retain(|x| !(x.ns == ns && x.name == new_key));
            new_members.push(Member {
                ns,
                name: new_key,
                binding: nb,
                from: Some(r),
            });
        }
        if let Some(t) = self.tables.get_mut(s as usize) {
            t.extend(new_members);
            t.sort_by_key(|x| (x.ns, x.name));
        }
    }

    fn charge(&mut self) -> Result<(), ResolveError> {
        if self.steps == 0 {
            return Err(ResolveError::BudgetExceeded {
                limit: Limit::MemberSteps,
            });
        }
        self.steps -= 1;
        Ok(())
    }

    /// The member of class `s` with key `key` in table `t`.
    fn own(&self, s: u32, t: u8, key: Name) -> Option<Member> {
        let table = self.tables.get(s as usize)?;
        let i = table
            .binary_search_by(|x| (x.ns, x.name).cmp(&(t, key)))
            .ok()?;
        table.get(i).copied()
    }

    fn found(m: &Model<'_>, member: Member, owner: u32) -> Option<Found> {
        let x = m.bindings.get(member.binding as usize)?;
        Some(Found {
            hit: Hit {
                res: x.res,
                kind: x.kind,
                vis: x.vis,
                binding: member.binding,
            },
            owner,
        })
    }

    fn outside_member(m: &Model<'_>, base: Res, t: u8, name: Name) -> Option<Found> {
        for ns in Namespace::ALL {
            if m.policy.table_ix(ns) != t {
                continue;
            }
            if let Some(e) = m.env.member(base, name, ns) {
                return Some(Found {
                    hit: Hit {
                        res: e.res,
                        kind: e.kind,
                        vis: e.vis,
                        binding: NONE,
                    },
                    owner: NONE,
                });
            }
        }
        None
    }

    /// Looks a member up in class `s` and its bases (C3 order), in tables
    /// `ts`; `name` is as written.
    pub(crate) fn lookup(
        &mut self,
        m: &Model<'_>,
        s: u32,
        ts: &[u8],
        name: Name,
    ) -> Result<Option<Found>, ResolveError> {
        for &t in ts {
            if let Some(f) = self.lookup_one(m, s, t, name)? {
                return Ok(Some(f));
            }
        }
        Ok(None)
    }

    fn lookup_one(
        &mut self,
        m: &Model<'_>,
        s: u32,
        t: u8,
        written: Name,
    ) -> Result<Option<Found>, ResolveError> {
        let name = m.fold.key(t, written);
        self.epoch = self.epoch.wrapping_add(1).max(1);
        let epoch = self.epoch;
        let mut chain: Vec<u32> = Vec::new();
        let mut cur = s;
        let result = loop {
            self.charge()?;
            if let Some(r) = self.memo.get(&(cur, t, name)) {
                break *r;
            }
            if let Some(member) = self.own(cur, t, name) {
                break Self::found(m, member, cur);
            }
            match self.stamp.get_mut(cur as usize) {
                Some(st) if *st == epoch => break None,
                Some(st) => *st = epoch,
                None => break None,
            }
            chain.push(cur);
            let bases = self.bases.get(cur as usize).map_or(&[][..], Vec::as_slice);
            match bases {
                [] => break None,
                [base] => {
                    let base = *base;
                    if let Some(next) = m.scope_of(base) {
                        cur = next;
                        continue;
                    }
                    break if m.is_outside(base) {
                        Self::outside_member(m, base, t, written)
                    } else {
                        None
                    };
                }
                _ => break self.in_order(m, cur, t, name, written)?,
            }
        };
        for c in chain {
            let _ = self.memo.insert((c, t, name), result);
        }
        Ok(result)
    }

    /// Searches a multi-base class's ancestors in its C3 order (`key` is
    /// the table key; `written` goes to the environment).
    fn in_order(
        &mut self,
        m: &Model<'_>,
        start: u32,
        t: u8,
        key: Name,
        written: Name,
    ) -> Result<Option<Found>, ResolveError> {
        let order: Vec<Res> = self
            .mro
            .get(start as usize)
            .and_then(Option::as_ref)
            .cloned()
            .unwrap_or_default();
        for base in order {
            self.charge()?;
            match m.scope_of(base) {
                Some(s) => {
                    if let Some(member) = self.own(s, t, key) {
                        return Ok(Self::found(m, member, s));
                    }
                }
                None if m.is_outside(base) => {
                    if let Some(f) = Self::outside_member(m, base, t, written) {
                        return Ok(Some(f));
                    }
                }
                None => {}
            }
        }
        Ok(None)
    }

    /// Looks a member up in class `s` and its ancestors as code inside `s`
    /// sees it unqualified: a member `s` may not use (an ancestor's private
    /// member) is not inherited, so the search goes on past it in method
    /// resolution order.
    fn lookup_usable(
        &mut self,
        m: &Model<'_>,
        s: u32,
        ts: &[u8],
        name: Name,
        module: u32,
    ) -> Result<Option<Found>, ResolveError> {
        let Some(first) = self.lookup(m, s, ts, name)? else {
            return Ok(None);
        };
        let ctx = TypeCtx::Type(s);
        if self.member_accessible(m, first, ctx, module)? {
            return Ok(Some(first));
        }
        // Rare: walk the whole order, skipping what `s` cannot use.
        let Some(me) = Self::class_res(m, s) else {
            return Ok(None);
        };
        let order = self.full_order(m, me)?;
        for &t in ts {
            for &c in &order {
                self.charge()?;
                let found = match m.scope_of(c) {
                    Some(cs) => {
                        let key = m.fold.key(t, name);
                        self.own(cs, t, key).and_then(|x| Self::found(m, x, cs))
                    }
                    None if m.is_outside(c) => Self::outside_member(m, c, t, name),
                    None => None,
                };
                if let Some(f) = found {
                    if self.member_accessible(m, f, ctx, module)? {
                        return Ok(Some(f));
                    }
                }
            }
        }
        Ok(None)
    }

    /// The C3 order of class scope `s` without itself (`None` for a class
    /// with fewer than two bases).
    #[cfg(test)]
    pub(crate) fn order(&self, s: u32) -> Option<&[Res]> {
        self.mro.get(s as usize)?.as_deref()
    }

    /// Whether class `a` is `b` or derives from it.
    fn derives(&mut self, m: &Model<'_>, a: u32, b: u32) -> Result<bool, ResolveError> {
        let mut seen: Vec<u32> = Vec::new();
        let mut stack = alloc::vec![a];
        while let Some(s) = stack.pop() {
            self.charge()?;
            if s == b {
                return Ok(true);
            }
            if seen.contains(&s) {
                continue;
            }
            seen.push(s);
            if let Some(bases) = self.bases.get(s as usize) {
                stack.extend(bases.iter().filter_map(|r| m.scope_of(*r)));
            }
        }
        Ok(false)
    }

    /// Whether a member found in `owner` with visibility `vis` may be used
    /// from type context `ctx` in module `module`.
    fn member_accessible(
        &mut self,
        m: &Model<'_>,
        f: Found,
        ctx: TypeCtx,
        module: u32,
    ) -> Result<bool, ResolveError> {
        if !m.policy.visibility_enforced() || f.owner == NONE {
            return Ok(true);
        }
        let here = match ctx {
            TypeCtx::Type(s) => Some(s),
            _ => None,
        };
        Ok(match f.hit.vis {
            Vis::Public => true,
            Vis::Package => {
                let home = m
                    .bindings
                    .get(f.hit.binding as usize)
                    .map_or(NONE, |b| b.home);
                m.accessible(Vis::Package, home, module)
            }
            Vis::Private => here == Some(f.owner),
            Vis::Protected => match here {
                Some(h) => self.derives(m, h, f.owner)? || self.derives(m, f.owner, h)?,
                None => false,
            },
        })
    }
}

/// Finishes the paths phase 3 deferred, now that member tables exist.
pub(crate) fn finish_deferred(
    m: &Model<'_>,
    members: &mut Members,
    outs: &mut [UnitOut],
) -> Result<(), ResolveError> {
    for u in 0..outs.len() {
        let deferred: Vec<Deferred> = outs
            .get_mut(u)
            .map(|o| core::mem::take(&mut o.deferred))
            .unwrap_or_default();
        let Some(unit) = m.units.get(u) else { continue };
        let Some(out) = outs.get_mut(u) else { continue };
        for d in deferred {
            finish_one(m, members, unit, out, d)?;
        }
    }
    Ok(())
}

fn finish_one(
    m: &Model<'_>,
    members: &mut Members,
    unit: &crate::model::Unit,
    out: &mut UnitOut,
    d: Deferred,
) -> Result<(), ResolveError> {
    let hir = &unit.hir;
    let path = *hir.path(d.path);
    let segs = hir.list(path.segments);
    let n = segs.len();
    let span = |k: usize| {
        segs.get(k)
            .map_or(hir.origin(NodeRef::Path(d.path)).span, |s| s.origin.span)
    };
    let type_directed = |out: &mut UnitOut| out.plan(d.path, Res::Unresolved, ix(n));
    // Where member lookup starts, and at which segment.
    let (container, first_seg): (Option<Res>, usize) = match d.kind {
        DeferKind::Lexical(f) => return finish_lexical(m, members, unit, out, d, f),
        DeferKind::Member { seg, container } => (Some(container.res), seg as usize),
        DeferKind::Root(root) => {
            let binding = match root {
                PathRoot::SelfType => m.policy.self_root(),
                PathRoot::ParentType => m.policy.parent_root(),
                _ => m.policy.static_root(),
            };
            if binding == RootBinding::Unsupported {
                out.diag(
                    unit.id,
                    d.path,
                    DiagKind::RootUnsupported { root },
                    span(0),
                    false,
                );
                return Ok(());
            }
            let class = match d.ctx {
                TypeCtx::None => {
                    out.diag(
                        unit.id,
                        d.path,
                        DiagKind::OutsideType { root },
                        span(0),
                        false,
                    );
                    return Ok(());
                }
                TypeCtx::Impl => {
                    type_directed(out);
                    return Ok(());
                }
                TypeCtx::Type(s) => s,
            };
            if binding == RootBinding::Late {
                type_directed(out);
                return Ok(());
            }
            let start = if root == PathRoot::ParentType {
                match members
                    .bases
                    .get(class as usize)
                    .and_then(|b| b.first())
                    .copied()
                {
                    None => {
                        out.diag(unit.id, d.path, DiagKind::NoParent, span(0), false);
                        return Ok(());
                    }
                    Some(base) => base,
                }
            } else {
                match m.scopes.get(class as usize).map(|s| s.kind) {
                    Some(ScopeKind::Type(item, _)) => Res::Def(hir_lang::DefId::foreign(
                        m.units
                            .get(m.scopes.get(class as usize).map_or(0, |s| s.unit) as usize)
                            .map_or(unit.id, |x| x.id),
                        hir_lang::Def::Item(item),
                    )),
                    _ => {
                        type_directed(out);
                        return Ok(());
                    }
                }
            };
            (Some(start), 0)
        }
    };
    let Some(container) = container else {
        return Ok(());
    };
    let Some(seg) = segs.get(first_seg).copied() else {
        return Ok(());
    };
    let last = first_seg + 1 == n;
    let ts = tables_for(&m.policy, path.ns, !last, d.callee);
    let found = if let Some(s) = m.scope_of(container) {
        members.lookup(m, s, &ts, seg.name)?
    } else if m.is_outside(container) {
        ts.iter()
            .find_map(|&t| Members::outside_member(m, container, t, seg.name))
    } else {
        None
    };
    let Some(f) = found else {
        // Not statically known: the type checker or the runtime decides.
        if matches!(d.kind, DeferKind::Root(_)) {
            type_directed(out);
        }
        return Ok(());
    };
    if !members.member_accessible(m, f, d.ctx, d.module)? {
        out.diag(
            unit.id,
            d.path,
            DiagKind::Private {
                name: seg.name,
                res: f.hit.res,
                vis: f.hit.vis,
            },
            span(first_seg),
            true,
        );
    }
    let via = NONE;
    if last {
        if !f.hit.kind.fits(path.ns) {
            out.diag(
                unit.id,
                d.path,
                DiagKind::WrongKind {
                    name: seg.name,
                    ns: path.ns,
                    found: f.hit.kind,
                },
                span(first_seg),
                false,
            );
            return Ok(());
        }
        out.segs.push(SegRef {
            path: d.path,
            seg: ix(first_seg),
            res: f.hit.res,
            via,
        });
        out.plan(d.path, f.hit.res, 0);
    } else if f.hit.kind.is_prefix() {
        out.segs.push(SegRef {
            path: d.path,
            seg: ix(first_seg),
            res: f.hit.res,
            via,
        });
        out.plan(d.path, f.hit.res, ix(n - first_seg - 1));
    } else {
        out.diag(
            unit.id,
            d.path,
            DiagKind::NotAContainer {
                name: seg.name,
                found: f.hit.kind,
            },
            span(first_seg),
            false,
        );
    }
    Ok(())
}

/// Finishes an unqualified name an inherited member may shadow: the first
/// class (innermost first) whose effective members or ancestors have an
/// accessible member of that name wins; otherwise the set-aside outcome of
/// resolving it as if nothing were inherited is committed unchanged.
fn finish_lexical(
    m: &Model<'_>,
    members: &mut Members,
    unit: &crate::model::Unit,
    out: &mut UnitOut,
    d: Deferred,
    f: u32,
) -> Result<(), ResolveError> {
    let fb = out
        .fallbacks
        .get_mut(f as usize)
        .map(core::mem::take)
        .unwrap_or_default();
    let hir = &unit.hir;
    let path = *hir.path(d.path);
    let segs = hir.list(path.segments);
    let n = segs.len();
    if let Some(seg) = segs.first().copied() {
        let last = n == 1;
        let ts = tables_for(&m.policy, path.ns, !last, d.callee);
        for &s in &fb.classes {
            let Some(found) = members.lookup_usable(m, s, &ts, seg.name, d.module)? else {
                continue;
            };
            let span = seg.origin.span;
            let seg_ref = SegRef {
                path: d.path,
                seg: 0,
                res: found.hit.res,
                via: NONE,
            };
            if let Some(pat) = fb.pat {
                // A bare identifier pattern matches a constant-like member
                // and otherwise binds.
                if found.hit.kind.is_pattern_constant() {
                    out.ident_matches.push(pat);
                    out.segs.push(seg_ref);
                    out.plan(d.path, found.hit.res, 0);
                }
                return Ok(());
            }
            if last {
                if found.hit.kind.fits(path.ns) {
                    out.segs.push(seg_ref);
                    out.plan(d.path, found.hit.res, 0);
                } else {
                    let kind = DiagKind::WrongKind {
                        name: seg.name,
                        ns: path.ns,
                        found: found.hit.kind,
                    };
                    out.diag(unit.id, d.path, kind, span, false);
                }
            } else if found.hit.kind.is_prefix() {
                out.segs.push(seg_ref);
                out.plan(d.path, found.hit.res, ix(n - 1));
            } else {
                let kind = DiagKind::NotAContainer {
                    name: seg.name,
                    found: found.hit.kind,
                };
                out.diag(unit.id, d.path, kind, span, false);
            }
            return Ok(());
        }
    }
    // Nothing inherited shadows it: commit what the walk found.
    if let Some(slot) = out.plan.get_mut(d.path.index()) {
        *slot = fb.plan;
    }
    if let Some(slot) = out.diagnosed.get_mut(d.path.index()) {
        *slot = fb.diagnosed;
    }
    out.segs.extend(fb.segs);
    out.diags.extend(fb.diags);
    out.ident_matches.extend(fb.ident_matches);
    for later in fb.deferred {
        finish_one(m, members, unit, out, later)?;
    }
    Ok(())
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use alloc::vec::Vec;

    use hir_lang::{ClassDef, Item, ItemId, ItemKind, Name, Ns, Path, Ty, TyId};

    use super::*;
    use crate::{model::fixture::*, policy::Policy};

    fn class(f: &mut Fixture, name: Name, bases: &[TyId], items: &[ItemId]) -> ItemId {
        let bases = f.b.list(bases);
        let items = f.b.list(items);
        f.b.item(Item::new(
            Some(name),
            ItemKind::Class(ClassDef {
                bases,
                items,
                ..ClassDef::default()
            }),
        ))
    }

    fn ty(f: &mut Fixture, name: Name) -> TyId {
        let p = f.b.name_path(name, Ns::Type);
        f.b.ty(Ty::Path(p))
    }

    /// class C0 { const K }  class C1 : C0 {}  ...  class C9 : C8 {}
    fn chain(f: &mut Fixture) -> (Vec<ItemId>, Name) {
        let k = f.name("K");
        let one = f.b.int(1);
        let kc = f.b.item(Item::new(
            Some(k),
            ItemKind::Const {
                ty: None,
                value: Some(one),
            },
        ));
        let mut classes = Vec::new();
        let c0 = f.name("C0");
        classes.push(class(f, c0, &[], &[kc]));
        for i in 1..10 {
            let base = f.name(&alloc::format!("C{}", i - 1));
            let t = ty(f, base);
            let n = f.name(&alloc::format!("C{i}"));
            classes.push(class(f, n, &[t], &[]));
        }
        (classes, k)
    }

    #[test]
    fn test_inherited_lookup_memoizes_the_chain() {
        let mut f = Fixture::new();
        let (classes, k) = chain(&mut f);
        let root = f.b.module(None, &classes);
        let hir = f.finish(root);
        let (mut m, outs) = walked(hir, &f.names, Policy::php());
        let mut members = Members::build(&mut m, &outs, u64::MAX).unwrap();
        let last = scope(&m, classes[9]);
        let t = m.policy.table_ix(Namespace::Const);
        let found = members.lookup(&m, last, &[t], k).unwrap().unwrap();
        assert_eq!(found.owner, scope(&m, classes[0]));
        // Every class walked on the way now answers from the memo.
        let spent = u64::MAX - members.steps;
        let middle = scope(&m, classes[5]);
        let again = members.lookup(&m, middle, &[t], k).unwrap().unwrap();
        assert_eq!(again.owner, found.owner);
        assert_eq!(u64::MAX - members.steps, spent + 1);
    }

    #[test]
    fn test_member_budget_and_cycles() {
        // class A : B {}  class B : A {}  — a lookup terminates.
        let mut f = Fixture::new();
        let (a, b, x) = (f.name("A"), f.name("B"), f.name("x"));
        let tb = ty(&mut f, b);
        let ca = class(&mut f, a, &[tb], &[]);
        let ta = ty(&mut f, a);
        let cb = class(&mut f, b, &[ta], &[]);
        let root = f.b.module(None, &[ca, cb]);
        let hir = f.finish(root);
        let (mut m, outs) = walked(hir, &f.names, Policy::php());
        let mut members = Members::build(&mut m, &outs, 100).unwrap();
        let s = scope(&m, ca);
        assert!(members.lookup(&m, s, &[0], x).unwrap().is_none());
        assert!(members.derives(&m, s, scope(&m, cb)).unwrap());
        let mut members = Members::build(&mut m, &outs, 1).unwrap();
        assert!(members.lookup(&m, s, &[0], x).is_err());
        let _ = Path::new(hir_lang::List::EMPTY, Ns::Value);
    }

    /// Builds classes from (name, bases) pairs, in order; each class gets a
    /// constant named after itself plus the extra constants listed.
    fn hierarchy(f: &mut Fixture, spec: &[(&str, &[&str], &[&str])]) -> (Vec<ItemId>, Vec<Name>) {
        let mut items = Vec::new();
        let mut names = Vec::new();
        for (name, bases, consts) in spec {
            let n = f.name(name);
            let tys: Vec<TyId> = bases
                .iter()
                .map(|b| {
                    let bn = f.name(b);
                    ty(f, bn)
                })
                .collect();
            let mut members = Vec::new();
            for c in *consts {
                let cn = f.name(c);
                let one = f.b.int(1);
                members.push(f.b.item(Item::new(
                    Some(cn),
                    ItemKind::Const {
                        ty: None,
                        value: Some(one),
                    },
                )));
            }
            items.push(class(f, n, &tys, &members));
            names.push(n);
        }
        (items, names)
    }

    fn res_of(m: &Model<'_>, item: ItemId) -> Res {
        Members::class_res(m, scope(m, item)).unwrap()
    }

    #[test]
    fn test_c3_matches_python_reference_example() {
        // The textbook hierarchy (Python docs, "The Python 2.3 MRO").
        let mut f = Fixture::new();
        let spec: &[(&str, &[&str], &[&str])] = &[
            ("O", &[], &[]),
            ("A", &["O"], &[]),
            ("B", &["O"], &[]),
            ("C", &["O"], &[]),
            ("D", &["O"], &[]),
            ("E", &["O"], &[]),
            ("K1", &["A", "B", "C"], &[]),
            ("K2", &["D", "B", "E"], &[]),
            ("K3", &["D", "A"], &[]),
            ("Z", &["K1", "K2", "K3"], &[]),
        ];
        let (items, _) = hierarchy(&mut f, spec);
        let root = f.b.module(None, &items);
        let hir = f.finish(root);
        let (mut m, outs) = walked(hir, &f.names, Policy::python());
        let members = Members::build(&mut m, &outs, u64::MAX).unwrap();
        let by = |i: usize| res_of(&m, items[i]);
        let z = members.order(scope(&m, items[9])).unwrap().to_vec();
        // Z, K1, K2, K3, D, A, B, C, E, O
        let want = [6, 7, 8, 4, 1, 2, 3, 5, 0].map(by);
        assert_eq!(z, want);
        let k1 = members.order(scope(&m, items[6])).unwrap().to_vec();
        assert_eq!(k1, [1, 2, 3, 0].map(by));
        assert!(m.diags.is_empty());
    }

    #[test]
    fn test_c3_diamond_differs_from_depth_first() {
        // class A { x }  class B(A)  class C(A) { x }  class D(B, C)
        // Depth-first would find A.x; C3 (D, B, C, A) finds C.x.
        let mut f = Fixture::new();
        let spec: &[(&str, &[&str], &[&str])] = &[
            ("A", &[], &["x"]),
            ("B", &["A"], &[]),
            ("C", &["A"], &["x"]),
            ("D", &["B", "C"], &[]),
        ];
        let (items, _) = hierarchy(&mut f, spec);
        let x = f.name("x");
        let root = f.b.module(None, &items);
        let hir = f.finish(root);
        let (mut m, outs) = walked(hir, &f.names, Policy::python());
        let mut members = Members::build(&mut m, &outs, u64::MAX).unwrap();
        let t = m.policy.table_ix(Namespace::Const);
        let d = scope(&m, items[3]);
        let found = members.lookup(&m, d, &[t], x).unwrap().unwrap();
        assert_eq!(found.owner, scope(&m, items[2]));
    }

    #[test]
    fn test_c3_reports_an_inconsistent_hierarchy_and_falls_back() {
        // class X  class Y(X)  class Z(X, Y): no consistent order (Python
        // raises TypeError); lookups still answer, depth-first.
        let mut f = Fixture::new();
        let spec: &[(&str, &[&str], &[&str])] = &[
            ("X", &[], &["k"]),
            ("Y", &["X"], &["k"]),
            ("Z", &["X", "Y"], &[]),
        ];
        let (items, names) = hierarchy(&mut f, spec);
        let k = f.name("k");
        let root = f.b.module(None, &items);
        let hir = f.finish(root);
        let (mut m, outs) = walked(hir, &f.names, Policy::python());
        let mut members = Members::build(&mut m, &outs, u64::MAX).unwrap();
        assert_eq!(m.diags.len(), 1);
        assert_eq!(
            m.diags[0].kind,
            DiagKind::InconsistentMro { class: names[2] }
        );
        let z = scope(&m, items[2]);
        let order = members.order(z).unwrap().to_vec();
        assert_eq!(order, [res_of(&m, items[0]), res_of(&m, items[1])]);
        let t = m.policy.table_ix(Namespace::Const);
        let found = members.lookup(&m, z, &[t], k).unwrap().unwrap();
        assert_eq!(found.owner, scope(&m, items[0]));
        // A repeated base is inconsistent too.
        let mut f = Fixture::new();
        let spec: &[(&str, &[&str], &[&str])] = &[("P", &[], &[]), ("Q", &["P", "P"], &[])];
        let (items, _) = hierarchy(&mut f, spec);
        let root = f.b.module(None, &items);
        let hir = f.finish(root);
        let (mut m, outs) = walked(hir, &f.names, Policy::python());
        let _ = Members::build(&mut m, &outs, u64::MAX).unwrap();
        assert!(matches!(m.diags[0].kind, DiagKind::InconsistentMro { .. }));
    }

    #[test]
    fn test_c3_terminates_on_cycles_and_respects_the_budget() {
        // class A(B, C)  class B(A, C)  class C — a cycle through two
        // multi-base classes: both get an order, nothing loops.
        let mut f = Fixture::new();
        let spec: &[(&str, &[&str], &[&str])] = &[
            ("A", &["B", "C"], &[]),
            ("B", &["A", "C"], &[]),
            ("C", &[], &[]),
        ];
        let (items, _) = hierarchy(&mut f, spec);
        let root = f.b.module(None, &items);
        let hir = f.finish(root);
        let (mut m, outs) = walked(hir.clone(), &f.names, Policy::python());
        let members = Members::build(&mut m, &outs, u64::MAX).unwrap();
        assert!(members.order(scope(&m, items[0])).is_some());
        assert!(members.order(scope(&m, items[1])).is_some());
        let (mut m, outs) = walked(hir, &f.names, Policy::python());
        assert!(Members::build(&mut m, &outs, 2).is_err());
    }
}
