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
//! Inherited lookups walk the base list. A class with exactly one base is
//! memoized for the whole chain it walks (so a long single-inheritance chain
//! costs O(1) amortized per distinct name); classes with several bases are
//! searched depth-first, left to right. Every step is charged to the
//! [`Budget`](crate::Budget).

use alloc::{collections::BTreeMap, vec::Vec};

use hir_lang::{
    ItemId, ItemKind, MixinAction, Name, NodeRef, Ns, PathId, PathRoot, Res, Span, Symbol, Ty,
    TyId, Vis,
};

use crate::{
    diag::DiagKind,
    env::{DefKind, env_members},
    error::{Limit, ResolveError},
    imports::Hit,
    model::{Binding, Model, NONE, Origin, ScopeKind, ix},
    pass::{DeferKind, Deferred, SegRef, TypeCtx, UnitOut},
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
    /// Effective member tables by scope index (empty for non-classes).
    pub(crate) tables: Vec<Vec<Member>>,
    /// Resolved bases by scope index.
    pub(crate) bases: Vec<Vec<Res>>,
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
    /// Builds every class's base list and effective member table.
    pub(crate) fn build(m: &mut Model<'_>, outs: &[UnitOut], steps: u64) -> Self {
        let n = m.scopes.len();
        let mut me = Self {
            tables: (0..n).map(|_| Vec::new()).collect(),
            bases: (0..n).map(|_| Vec::new()).collect(),
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
                        name: x.name,
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
        me
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
                let b = m.push_binding(Binding {
                    ns: t,
                    name,
                    res: e.res,
                    kind: e.kind,
                    vis: e.vis,
                    home: s,
                    origin: Origin::Env,
                    hoist: Hoist::Scope,
                    shadowed: false,
                    span: Span::empty(0),
                });
                members.push((t, name, b));
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
        let find = |sources: &[Source], from: Option<Res>, sym: Symbol| {
            sources
                .iter()
                .filter(|(r, _)| from.is_none_or(|f| f == *r))
                .flat_map(|(r, list)| list.iter().map(move |x| (*r, *x)))
                .find(|(_, (_, name, _))| name.sym == sym && name.mark.is_root())
        };
        let mut excluded: Vec<(Res, Symbol)> = Vec::new();
        let mut aliases: Vec<AliasRule> = Vec::new();
        for rule in &rules {
            let from = rule.from.and_then(|t| ty_res(m, outs, u, t));
            let Some(found) = find(&sources, from, rule.method.sym) else {
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
                if excluded.iter().any(|(r, sym)| r == res && *sym == name.sym)
                    || is_own((ns, name))
                {
                    continue;
                }
                if let Some(&(_, _, first, _)) = added.iter().find(|x| x.0 == ns && x.1 == name) {
                    let fr = m.bindings.get(first as usize).map(|x| x.res);
                    let sr = m.bindings.get(b as usize).map(|x| x.res);
                    if let (Some(Res::Def(fd)), Some(Res::Def(sd))) = (fr, sr) {
                        if fd != sd {
                            conflicts.push((name, fd, sd));
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
            let new_name = alias.map_or(name, |a| Name::new(a.sym));
            if is_own((ns, new_name)) {
                continue;
            }
            let nb = m.push_binding(Binding {
                name: new_name,
                vis: vis.unwrap_or(orig.vis),
                home: s,
                origin: Origin::Mixin(b),
                span: alias.map_or(orig.span, |a| a.span),
                ..orig
            });
            new_members.retain(|x| !(x.ns == ns && x.name == new_name));
            new_members.push(Member {
                ns,
                name: new_name,
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

    fn own(&self, s: u32, t: u8, name: Name) -> Option<Member> {
        let table = self.tables.get(s as usize)?;
        let i = table
            .binary_search_by(|x| (x.ns, x.name).cmp(&(t, name)))
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

    /// Looks a member up in class `s` and its bases, in tables `ts`.
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
        name: Name,
    ) -> Result<Option<Found>, ResolveError> {
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
                        Self::outside_member(m, base, t, name)
                    } else {
                        None
                    };
                }
                _ => break self.dfs(m, cur, t, name)?,
            }
        };
        for c in chain {
            let _ = self.memo.insert((c, t, name), result);
        }
        Ok(result)
    }

    /// Depth-first search over several bases, left to right.
    fn dfs(
        &mut self,
        m: &Model<'_>,
        start: u32,
        t: u8,
        name: Name,
    ) -> Result<Option<Found>, ResolveError> {
        let mut seen: Vec<u32> = alloc::vec![start];
        let mut stack: Vec<Res> = self
            .bases
            .get(start as usize)
            .map(|b| b.iter().rev().copied().collect())
            .unwrap_or_default();
        while let Some(base) = stack.pop() {
            self.charge()?;
            let Some(s) = m.scope_of(base) else {
                if m.is_outside(base) {
                    if let Some(f) = Self::outside_member(m, base, t, name) {
                        return Ok(Some(f));
                    }
                }
                continue;
            };
            if seen.contains(&s) {
                continue;
            }
            seen.push(s);
            if let Some(member) = self.own(s, t, name) {
                return Ok(Self::found(m, member, s));
            }
            if let Some(b) = self.bases.get(s as usize) {
                stack.extend(b.iter().rev().copied());
            }
        }
        Ok(None)
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

fn tables_for(m: &Model<'_>, ns: Ns, prefix: bool) -> Vec<u8> {
    let list: &[Namespace] = if prefix {
        &[Namespace::Module, Namespace::Type]
    } else {
        match ns {
            Ns::Value | Ns::Pattern => &[Namespace::Value],
            Ns::Type => &[Namespace::Type],
            Ns::Region => &[],
            Ns::Import => &[
                Namespace::Value,
                Namespace::Type,
                Namespace::Module,
                Namespace::Macro,
            ],
        }
    };
    let mut out = Vec::new();
    for ns in list {
        let t = m.policy.table_ix(*ns);
        if !out.contains(&t) {
            out.push(t);
        }
    }
    out
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
    let ts = tables_for(m, path.ns, !last);
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
        let mut members = Members::build(&mut m, &outs, u64::MAX);
        let last = scope(&m, classes[9]);
        let t = m.policy.table_ix(Namespace::Value);
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
        let mut members = Members::build(&mut m, &outs, 100);
        let s = scope(&m, ca);
        assert!(members.lookup(&m, s, &[0], x).unwrap().is_none());
        assert!(members.derives(&m, s, scope(&m, cb)).unwrap());
        let mut members = Members::build(&mut m, &outs, 1);
        assert!(members.lookup(&m, s, &[0], x).is_err());
        let _ = Path::new(hir_lang::List::EMPTY, Ns::Value);
    }
}
