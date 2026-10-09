//! Phase 1: collect every unit's item scopes, definitions, and imports.
//!
//! One walk per unit, driven by hir-lang's scope events: an item belongs to
//! the scope that is innermost when the walk enters it (a module's item list,
//! a class or interface body, or a block's item statements), so the scope
//! structure is read from the walk rather than re-derived.

use alloc::vec::Vec;

use hir_lang::{
    Control, Event, Expr, ExprId, Frame, Hir, IdKind, Item, ItemId, ItemKind, Name, NodeRef, Res,
    Span, Stmt, Symbol, VariantId,
};

use crate::{
    diag::DiagKind,
    env::DefKind,
    model::{Binding, Import, ImportState, NONE, Origin, Scope, ScopeKind, ix},
    policy::{Hoist, ItemClass, Namespace, Policy},
};

/// What one unit contributes, with indexes already offset into the model's
/// vectors.
pub(crate) struct Collected {
    pub(crate) scopes: Vec<Scope>,
    pub(crate) bindings: Vec<Binding>,
    pub(crate) imports: Vec<Import>,
    pub(crate) sums: Vec<Vec<(Symbol, VariantId)>>,
    pub(crate) root_scope: u32,
    pub(crate) item_scope: Vec<u32>,
    pub(crate) block_scope: Vec<u32>,
    pub(crate) sum_table: Vec<u32>,
    pub(crate) import_of: Vec<u32>,
    /// (kind, span, node) problems found while collecting.
    pub(crate) diags: Vec<(DiagKind, Span, NodeRef)>,
}

/// Offsets of this unit's records in the model.
#[derive(Clone, Copy)]
pub(crate) struct Bases {
    pub(crate) unit: u32,
    pub(crate) scope: u32,
    pub(crate) binding: u32,
    pub(crate) import: u32,
    pub(crate) sum: u32,
}

/// The span to report for an item's name: its recorded name span, or the
/// item's own span when lowering left the name span unset.
pub(crate) fn item_name_span(hir: &Hir, item: ItemId) -> Span {
    let span = hir.item(item).name_span;
    if span == Span::empty(0) {
        hir.origin(NodeRef::Item(item)).span
    } else {
        span
    }
}

/// What the next `ScopeOpen` belongs to.
#[derive(Clone, Copy)]
enum Pending {
    None,
    Block(ExprId),
    Item(ItemId),
}

struct Collector<'a> {
    hir: &'a Hir,
    policy: &'a Policy,
    bases: Bases,
    out: Collected,
    /// Per open scope: its table (local index) or `NONE`.
    open: Vec<u32>,
    /// The open table scopes only (local indexes).
    tables: Vec<u32>,
    pending: Pending,
    module_counter: u32,
}

/// Collects one unit.
pub(crate) fn collect(hir: &Hir, policy: &Policy, bases: Bases) -> Collected {
    let n_items = hir.count(IdKind::Item);
    let n_exprs = hir.count(IdKind::Expr);
    let mut c = Collector {
        hir,
        policy,
        bases,
        out: Collected {
            scopes: Vec::new(),
            bindings: Vec::new(),
            imports: Vec::new(),
            sums: Vec::new(),
            root_scope: NONE,
            item_scope: alloc::vec![NONE; n_items],
            block_scope: alloc::vec![NONE; n_exprs],
            sum_table: alloc::vec![NONE; n_items],
            import_of: alloc::vec![NONE; n_items],
            diags: Vec::new(),
        },
        open: Vec::new(),
        tables: Vec::new(),
        pending: Pending::None,
        module_counter: 0,
    };
    let root = hir.root();
    hir.walk_from(NodeRef::Item(root), |ev| {
        c.event(ev);
        Control::Continue
    });
    c.out.root_scope = c.out.item_scope.get(root.index()).copied().unwrap_or(NONE);
    c.mark_duplicates();
    c.out
}

impl Collector<'_> {
    fn event(&mut self, ev: Event) {
        match ev {
            Event::Enter(node) => {
                self.pending = Pending::None;
                match node {
                    NodeRef::Item(i) => self.enter_item(i),
                    NodeRef::Expr(e) => {
                        if let Expr::Block(b) = self.hir.expr(e) {
                            let has_items = self
                                .hir
                                .list(b.stmts)
                                .iter()
                                .any(|s| matches!(self.hir.stmt(*s), Stmt::Item(_)));
                            if has_items {
                                self.pending = Pending::Block(e);
                            }
                        }
                    }
                    _ => {}
                }
            }
            Event::FrameOpen(Frame::Item(i)) => self.pending = Pending::Item(i),
            Event::ScopeOpen => {
                let table = match core::mem::replace(&mut self.pending, Pending::None) {
                    Pending::Block(e) => self.new_scope(ScopeKind::Block, Some(e), None),
                    Pending::Item(i) => match &self.hir.item(i).kind {
                        ItemKind::Module { .. } => {
                            self.new_scope(ScopeKind::Module(i), None, Some(i))
                        }
                        ItemKind::Class(_) => {
                            self.new_scope(ScopeKind::Type(i, true), None, Some(i))
                        }
                        ItemKind::Interface(_) => {
                            self.new_scope(ScopeKind::Type(i, false), None, Some(i))
                        }
                        _ => NONE,
                    },
                    Pending::None => NONE,
                };
                self.open.push(table);
                if table != NONE {
                    self.tables.push(table);
                }
            }
            Event::ScopeClose => {
                if let Some(t) = self.open.pop() {
                    if t != NONE {
                        let _ = self.tables.pop();
                        let counter = self.module_counter;
                        if let Some(s) = self.out.scopes.get_mut(t as usize) {
                            if matches!(s.kind, ScopeKind::Module(_)) {
                                s.post = counter;
                            }
                        }
                    }
                }
            }
            _ => self.pending = Pending::None,
        }
    }

    /// Creates a table scope (local index) under the innermost open table.
    fn new_scope(&mut self, kind: ScopeKind, block: Option<ExprId>, item: Option<ItemId>) -> u32 {
        let local = ix(self.out.scopes.len());
        let global = self.bases.scope + local;
        let parent_local = self.tables.last().copied();
        let parent = parent_local.map_or(NONE, |p| self.bases.scope + p);
        let parent_module = parent_local
            .and_then(|p| self.out.scopes.get(p as usize))
            .map_or(NONE, |s| s.module);
        let (module, pre) = if matches!(kind, ScopeKind::Module(_)) {
            let pre = self.module_counter;
            self.module_counter += 1;
            (global, pre)
        } else {
            (parent_module, 0)
        };
        self.out.scopes.push(Scope {
            unit: self.bases.unit,
            kind,
            parent,
            module,
            pre,
            post: pre.saturating_add(1),
            defs: Vec::new(),
            named: Vec::new(),
            globs: Vec::new(),
            mixin_uses: Vec::new(),
            table: Vec::new(),
        });
        if let Some(e) = block {
            if let Some(slot) = self.out.block_scope.get_mut(e.index()) {
                *slot = global;
            }
        }
        if let Some(i) = item {
            if let Some(slot) = self.out.item_scope.get_mut(i.index()) {
                *slot = global;
            }
        }
        local
    }

    /// The innermost open scope, if it is a table (local index).
    fn container(&self) -> Option<u32> {
        self.open.last().copied().filter(|t| *t != NONE)
    }

    fn enter_item(&mut self, i: ItemId) {
        let Some(container) = self.container() else {
            return;
        };
        let item = *self.hir.item(i);
        let container_kind = self.out.scopes.get(container as usize).map(|s| s.kind);
        match item.kind {
            ItemKind::Import { path, glob } => self.import(container, i, &item, path, glob),
            ItemKind::MixinUse(_) => {
                if let Some(s) = self.out.scopes.get_mut(container as usize) {
                    s.mixin_uses.push(i);
                }
            }
            ItemKind::Impl(_) => {}
            ref kind => {
                let Some(name) = item.name else { return };
                let class = ItemClass::of(kind);
                let Some(def_kind) = DefKind::of_item(kind) else {
                    return;
                };
                let mut hoist = class.map_or(Hoist::Scope, |c| self.policy.hoisting(c));
                let mut home = container;
                let is_member = matches!(container_kind, Some(ScopeKind::Type(..)));
                if hoist == Hoist::Module {
                    if !is_member {
                        let module = self
                            .out
                            .scopes
                            .get(container as usize)
                            .map_or(NONE, |s| s.module);
                        if module != NONE {
                            home = module - self.bases.scope;
                        }
                    }
                    hoist = Hoist::Scope;
                }
                let occupies = match class {
                    Some(c) => self.policy.occupies(c),
                    None => crate::policy::NsSet::of(&[
                        Namespace::Value,
                        Namespace::Type,
                        Namespace::Module,
                    ]),
                };
                if let ItemKind::Sum(sum) = kind {
                    let mut table: Vec<(Symbol, VariantId)> = self
                        .hir
                        .list(sum.variants)
                        .iter()
                        .filter_map(|v| self.hir.variant(*v).map(|var| (var.name.sym, *v)))
                        .collect();
                    table.sort_by_key(|(s, _)| *s);
                    let t = self.bases.sum + ix(self.out.sums.len());
                    self.out.sums.push(table);
                    if let Some(slot) = self.out.sum_table.get_mut(i.index()) {
                        *slot = t;
                    }
                }
                let span = crate::collect::item_name_span(self.hir, i);
                let res = Res::Def(hir_lang::DefId::foreign(
                    self.hir.unit(),
                    hir_lang::Def::Item(i),
                ));
                let mut seen = [false; 5];
                for ns in occupies.iter() {
                    let t = self.policy.table_ix(ns);
                    let Some(slot) = seen.get_mut(t as usize) else {
                        continue;
                    };
                    if core::mem::replace(slot, true) {
                        continue;
                    }
                    let b = ix(self.out.bindings.len()) + self.bases.binding;
                    self.out.bindings.push(Binding {
                        ns: t,
                        name,
                        res,
                        kind: def_kind,
                        vis: item.vis,
                        home: home + self.bases.scope,
                        origin: Origin::Item(i),
                        hoist,
                        shadowed: false,
                        span,
                    });
                    if let Some(s) = self.out.scopes.get_mut(home as usize) {
                        s.defs.push(b);
                    }
                }
            }
        }
    }

    fn import(
        &mut self,
        container: u32,
        i: ItemId,
        item: &Item,
        path: hir_lang::PathId,
        glob: bool,
    ) {
        let p = self.hir.path(path);
        let last = self.hir.list(p.segments).last().map(|s| s.name);
        let name: Option<Name> = if glob { None } else { item.name.or(last) };
        let alias = !glob && item.name.is_some() && item.name != last;
        let span = item_name_span(self.hir, i);
        let mut state = ImportState::Pending;
        if glob && !self.policy.globs_allowed() {
            self.out
                .diags
                .push((DiagKind::GlobsUnsupported, span, NodeRef::Item(i)));
            state = ImportState::Failed;
        }
        if alias && !self.policy.aliases_allowed() {
            self.out
                .diags
                .push((DiagKind::AliasesUnsupported, span, NodeRef::Item(i)));
        }
        if p.segments.is_empty() {
            state = ImportState::Failed;
        }
        let import = self.bases.import + ix(self.out.imports.len());
        self.out.imports.push(Import {
            unit: self.bases.unit,
            item: i,
            path,
            scope: container + self.bases.scope,
            glob,
            name,
            vis: self.policy.import_vis(item.vis),
            state,
            res: Res::Err,
            unresolved: 0,
            late: false,
            segs: Vec::new(),
        });
        if let Some(slot) = self.out.import_of.get_mut(i.index()) {
            *slot = import;
        }
        if let Some(s) = self.out.scopes.get_mut(container as usize) {
            if glob {
                s.globs.push(import);
            } else {
                s.named.push(import);
            }
        }
    }

    /// Applies the redefinition rule to every scope's definitions.
    fn mark_duplicates(&mut self) {
        let base = self.bases.binding;
        let last_wins = self.policy.redefinition() == crate::policy::Redefinition::LastWins;
        let mut order: Vec<u32> = Vec::new();
        let mut reported: Vec<(ItemId, Span)> = Vec::new();
        for s in 0..self.out.scopes.len() {
            order.clear();
            if let Some(scope) = self.out.scopes.get(s) {
                order.extend_from_slice(&scope.defs);
            }
            let key = |b: u32, bs: &[Binding]| bs.get((b - base) as usize).map(|b| (b.ns, b.name));
            // Stable: equal names keep declaration order.
            order.sort_by_key(|b| key(*b, &self.out.bindings));
            let mut i = 0;
            while i < order.len() {
                let k = order.get(i).and_then(|b| key(*b, &self.out.bindings));
                let mut j = i + 1;
                while j < order.len() && order.get(j).and_then(|b| key(*b, &self.out.bindings)) == k
                {
                    j += 1;
                }
                if j - i > 1 && !last_wins {
                    let first = order
                        .get(i)
                        .and_then(|b| self.out.bindings.get((*b - base) as usize))
                        .map(|b| b.span);
                    for &dup in order.get(i + 1..j).unwrap_or(&[]) {
                        if let Some(b) = self.out.bindings.get_mut((dup - base) as usize) {
                            b.shadowed = true;
                            if let (Origin::Item(item), Some(first)) = (b.origin, first) {
                                reported.push((item, first));
                            }
                        }
                    }
                }
                i = j;
            }
        }
        reported.sort_by_key(|(i, _)| *i);
        reported.dedup_by_key(|(i, _)| *i);
        for (item, first) in reported {
            let name = self.hir.item(item).name;
            if let Some(name) = name {
                self.out.diags.push((
                    DiagKind::Duplicate { name, first },
                    item_name_span(self.hir, item),
                    NodeRef::Item(item),
                ));
            }
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use hir_lang::{Item, ItemKind, Ns, Path, Segment, Stmt};

    use crate::{
        diag::DiagKind,
        model::{ImportState, fixture::*},
        policy::{Policy, Reexport},
    };

    #[test]
    fn test_duplicates_keep_first_unless_last_wins() {
        let mut f = Fixture::new();
        let n = f.name("f");
        let b1 = f.b.block(&[], None);
        let f1 = f.b.func(n, &[], b1);
        let b2 = f.b.block(&[], None);
        let f2 = f.b.func(n, &[], b2);
        let root = f.b.module(None, &[f1, f2]);
        let hir = f.finish(root);
        let m = model(hir.clone(), &f.names, Policy::new());
        let shadowed: alloc::vec::Vec<bool> = m.bindings.iter().map(|b| b.shadowed).collect();
        assert_eq!(shadowed, [false, true]);
        assert!(matches!(m.diags[0].kind, DiagKind::Duplicate { .. }));
        let m = model(hir, &f.names, Policy::python());
        assert!(m.bindings.iter().all(|b| !b.shadowed));
        assert!(m.diags.is_empty());
    }

    #[test]
    fn test_module_hoisting_moves_block_items_to_the_module() {
        // fn main() { { fn late() {} } }  under PHP rules
        let mut f = Fixture::new();
        let (late, main) = (f.name("late"), f.name("main"));
        let lb = f.b.block(&[], None);
        let l = f.b.func(late, &[], lb);
        let s = f.b.stmt(Stmt::Item(l));
        let inner = f.b.block(&[s], None);
        let si = f.b.expr_stmt(inner);
        let body = f.b.block(&[si], None);
        let mf = f.b.func(main, &[], body);
        let root = f.b.module(None, &[mf]);
        let hir = f.finish(root);
        let m = model(hir.clone(), &f.names, Policy::php());
        let home = m.bindings.iter().find(|b| b.name == late).unwrap().home;
        assert_eq!(home, scope(&m, root));
        let m = model(hir, &f.names, Policy::kraken());
        let home = m.bindings.iter().find(|b| b.name == late).unwrap().home;
        assert_ne!(home, scope(&m, root));
    }

    #[test]
    fn test_import_records_names_and_policy_rejections() {
        let mut f = Fixture::new();
        let (m_, x, y) = (f.name("m"), f.name("x"), f.name("y"));
        let mk = |f: &mut Fixture, parts: &[hir_lang::Name]| {
            let segs: alloc::vec::Vec<Segment> = parts
                .iter()
                .map(|n| Segment::new(*n, f.b.origin()))
                .collect();
            let segs = f.b.list(&segs);
            f.b.path(Path::new(segs, Ns::Import))
        };
        let p1 = mk(&mut f, &[m_, x]);
        let plain = f.b.item(Item::new(
            None,
            ItemKind::Import {
                path: p1,
                glob: false,
            },
        ));
        let p2 = mk(&mut f, &[m_, x]);
        let aliased = f.b.item(Item::new(
            Some(y),
            ItemKind::Import {
                path: p2,
                glob: false,
            },
        ));
        let p3 = mk(&mut f, &[m_]);
        let glob = f.b.item(Item::new(
            None,
            ItemKind::Import {
                path: p3,
                glob: true,
            },
        ));
        let root = f.b.module(None, &[plain, aliased, glob]);
        let hir = f.finish(root);
        let policy = Policy::new().with_imports(false, false, Reexport::AsDeclared);
        let m = model(hir, &f.names, policy);
        let names: alloc::vec::Vec<_> = m.imports.iter().map(|i| i.name).collect();
        assert_eq!(names, [Some(x), Some(y), None]);
        assert_eq!(m.imports[2].state, ImportState::Failed);
        let kinds: alloc::vec::Vec<_> = m.diags.iter().map(|d| d.kind).collect();
        assert!(kinds.contains(&DiagKind::AliasesUnsupported));
        assert!(kinds.contains(&DiagKind::GlobsUnsupported));
    }
}
