//! The program-wide data every phase shares: units, scope tables, bindings,
//! imports. All indexes are dense `u32`s into vectors; `NONE` marks absence.

use alloc::vec::Vec;
use core::cmp::Ordering;

use hir_lang::{Def, DefId, Hir, ItemId, Name, PathId, Res, Span, Symbol, UnitId, VariantId, Vis};

use crate::{
    diag::{DiagKind, Diagnostic},
    env::{DefKind, Env},
    policy::{Hoist, Policy},
};

/// "No index".
pub(crate) const NONE: u32 = u32::MAX;

/// The table index that stands for "any namespace" (failed imports, whose
/// namespaces are unknown).
pub(crate) const ANY_NS: u8 = u8::MAX;

/// Converts a length to a `u32` index, saturating (HIR arenas are bounded by
/// `u32::MAX - 1`, so saturation never happens for valid input).
#[inline]
pub(crate) fn ix(n: usize) -> u32 {
    u32::try_from(n).unwrap_or(NONE)
}

/// One compilation unit of the program.
pub(crate) struct Unit {
    pub(crate) id: UnitId,
    /// The root name other units reach this unit by, if any.
    pub(crate) name: Option<Name>,
    pub(crate) package: u32,
    pub(crate) hir: Hir,
    pub(crate) root_scope: u32,
    /// By item index: the table of a module, class, or interface item.
    pub(crate) item_scope: Vec<u32>,
    /// By expression index: the table of a block holding items.
    pub(crate) block_scope: Vec<u32>,
    /// By item index: the sum's variant table in `Model::sums`.
    pub(crate) sum_table: Vec<u32>,
    /// By item index: the import record of an import item.
    pub(crate) import_of: Vec<u32>,
    /// Table entries visible only from their gating item on (hoisting
    /// `AfterDecl`), sorted by gating item index: (item, scope, entry).
    pub(crate) after_decl: Vec<(u32, u32, u32)>,
}

/// What a table scope belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ScopeKind {
    Module(ItemId),
    /// A class (`true`) or interface (`false`): member tables.
    Type(ItemId, bool),
    Block,
}

/// A scope that holds named items: a module, a class or interface, or a block
/// with item statements.
pub(crate) struct Scope {
    pub(crate) unit: u32,
    pub(crate) kind: ScopeKind,
    /// The innermost enclosing table scope.
    pub(crate) parent: u32,
    /// The enclosing module scope (itself for a module).
    pub(crate) module: u32,
    /// Preorder interval among the unit's module scopes, for "is a
    /// descendant of" in O(1). Meaningful for modules only.
    pub(crate) pre: u32,
    pub(crate) post: u32,
    /// Definitions, in declaration order.
    pub(crate) defs: Vec<u32>,
    /// Named and glob imports declared here.
    pub(crate) named: Vec<u32>,
    pub(crate) globs: Vec<u32>,
    /// Mixin-use items (classes only).
    pub(crate) mixin_uses: Vec<ItemId>,
    /// The final table, sorted by (ns, name), built after import resolution.
    pub(crate) table: Vec<Entry>,
}

/// Where a binding came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Origin {
    /// An item of the home scope's unit.
    Item(ItemId),
    /// A named import (import index).
    Import(u32),
    /// A glob import (import index) carrying another binding.
    Glob(u32, u32),
    /// A sum variant carried by a glob import of the sum.
    Variant(u32, VariantId),
    /// An environment export (glob of an outside container, a mixin of an
    /// outside class).
    Env,
    /// A member brought in by a mixin rule (the original binding).
    Mixin(u32),
}

/// One name in one table.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Binding {
    pub(crate) ns: u8,
    pub(crate) name: Name,
    pub(crate) res: Res,
    pub(crate) kind: DefKind,
    pub(crate) vis: Vis,
    pub(crate) home: u32,
    pub(crate) origin: Origin,
    pub(crate) hoist: Hoist,
    /// A duplicate dropped by the redefinition rule.
    pub(crate) shadowed: bool,
    /// The name's location (for duplicate reports).
    pub(crate) span: Span,
}

/// The state of a name in a finished table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EntryState {
    One(u32),
    Ambiguous(u32, u32),
    /// A named import of this name failed (any namespace).
    Failed(u32),
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Entry {
    pub(crate) ns: u8,
    pub(crate) name: Name,
    pub(crate) state: EntryState,
}

/// An import's progress.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ImportState {
    Pending,
    Done,
    Failed,
}

/// One import item.
pub(crate) struct Import {
    pub(crate) unit: u32,
    pub(crate) item: ItemId,
    pub(crate) path: PathId,
    pub(crate) scope: u32,
    pub(crate) glob: bool,
    /// The bound name (alias or last segment) of a named import.
    pub(crate) name: Option<Name>,
    /// The effective export visibility.
    pub(crate) vis: Vis,
    pub(crate) state: ImportState,
    /// The resolution written to the import's path, and its unresolved count.
    pub(crate) res: Res,
    pub(crate) unresolved: u32,
    /// Resolved in the final (fallback) mode: rechecked at the end.
    pub(crate) late: bool,
    /// Segment references for the index: (segment, resolution, binding).
    pub(crate) segs: Vec<(u32, Res, u32)>,
}

/// Everything the phases share.
pub(crate) struct Model<'e> {
    pub(crate) policy: Policy,
    pub(crate) env: &'e dyn Env,
    pub(crate) units: Vec<Unit>,
    /// (unit id, unit index), sorted, for `DefId` lookups.
    pub(crate) unit_ix: Vec<(UnitId, u32)>,
    /// (root name, unit index), sorted.
    pub(crate) roots: Vec<(Name, u32)>,
    pub(crate) scopes: Vec<Scope>,
    pub(crate) bindings: Vec<Binding>,
    pub(crate) imports: Vec<Import>,
    /// Variant tables of sums: (symbol, variant), sorted by symbol.
    pub(crate) sums: Vec<Vec<(Symbol, VariantId)>>,
    pub(crate) diags: Vec<Diagnostic>,
}

impl Model<'_> {
    /// The unit index of a unit id, if it is part of the program.
    pub(crate) fn unit_of(&self, id: UnitId) -> Option<u32> {
        self.unit_ix
            .binary_search_by(|(u, _)| u.cmp(&id))
            .ok()
            .and_then(|i| self.unit_ix.get(i))
            .map(|(_, i)| *i)
    }

    /// The program-local item a `DefId` names: (unit index, item).
    pub(crate) fn local_item(&self, d: DefId) -> Option<(u32, ItemId)> {
        let u = self.unit_of(d.unit())?;
        match d.def() {
            Def::Item(i) => self.units.get(u as usize)?.hir.get_item(i).map(|_| (u, i)),
            Def::Variant(_) => None,
        }
    }

    /// The table scope a resolution opens, if it is a program module, class,
    /// or interface.
    pub(crate) fn scope_of(&self, res: Res) -> Option<u32> {
        let Res::Def(d) = res else { return None };
        let (u, item) = self.local_item(d)?;
        let s = *self.units.get(u as usize)?.item_scope.get(item.index())?;
        (s != NONE).then_some(s)
    }

    /// The variant table of a program sum.
    pub(crate) fn sum_of(&self, res: Res) -> Option<(u32, u32)> {
        let Res::Def(d) = res else { return None };
        let (u, item) = self.local_item(d)?;
        let t = *self.units.get(u as usize)?.sum_table.get(item.index())?;
        (t != NONE).then_some((u, t))
    }

    /// Whether `res` names something defined outside the program (so the
    /// environment answers questions about its members).
    pub(crate) fn is_outside(&self, res: Res) -> bool {
        match res {
            Res::Def(d) => self.unit_of(d.unit()).is_none(),
            Res::Extern(_) => true,
            _ => false,
        }
    }

    /// The kind of a program definition.
    pub(crate) fn kind_of_def(&self, d: DefId) -> Option<DefKind> {
        let u = self.unit_of(d.unit())?;
        let hir = &self.units.get(u as usize)?.hir;
        match d.def() {
            Def::Item(i) => DefKind::of_item(&hir.get_item(i)?.kind),
            Def::Variant(v) => hir.variant(v).map(|v| DefKind::Variant {
                unit: v.shape == hir_lang::Shape::Unit,
            }),
        }
    }

    /// Looks a name up in a finished table: the exact namespace, else a failed
    /// import of that name.
    pub(crate) fn find(&self, scope: u32, ns: u8, name: Name) -> Option<EntryState> {
        let table = &self.scopes.get(scope as usize)?.table;
        let key = |e: &Entry| (e.ns, e.name).cmp(&(ns, name));
        if let Ok(i) = table.binary_search_by(key) {
            return table.get(i).map(|e| e.state);
        }
        let any = |e: &Entry| (e.ns, e.name).cmp(&(ANY_NS, name));
        table
            .binary_search_by(any)
            .ok()
            .and_then(|i| table.get(i))
            .map(|e| e.state)
    }

    /// Whether module scope `inner` is `outer` or nested in it.
    pub(crate) fn within(&self, inner: u32, outer: u32) -> bool {
        if inner == outer {
            return true;
        }
        match (
            self.scopes.get(inner as usize),
            self.scopes.get(outer as usize),
        ) {
            (Some(i), Some(o)) => i.unit == o.unit && o.pre <= i.pre && i.pre < o.post,
            _ => false,
        }
    }

    /// Whether a binding with visibility `vis` defined in `home` may be used
    /// from scope `from` (module rules; class-member rules live in the
    /// member phase).
    pub(crate) fn accessible(&self, vis: Vis, home: u32, from: u32) -> bool {
        if !self.policy.visibility_enforced() {
            return true;
        }
        let module = |s: u32| self.scopes.get(s as usize).map_or(NONE, |s| s.module);
        let (hm, fm) = (module(home), module(from));
        match vis {
            Vis::Public => true,
            Vis::Package => {
                let pkg = |s: u32| {
                    self.scopes
                        .get(s as usize)
                        .and_then(|s| self.units.get(s.unit as usize))
                        .map(|u| u.package)
                };
                pkg(home) == pkg(from)
            }
            Vis::Private | Vis::Protected => {
                hm == fm || (self.policy.private_to_descendants() && self.within(fm, hm))
            }
        }
    }

    /// The `DefId` of an item of unit `u`.
    pub(crate) fn def_id(&self, u: u32, def: Def) -> DefId {
        let unit = self.units.get(u as usize).map_or(UnitId::new(0), |u| u.id);
        DefId::foreign(unit, def)
    }

    pub(crate) fn push_binding(&mut self, b: Binding) -> u32 {
        let i = ix(self.bindings.len());
        self.bindings.push(b);
        i
    }

    pub(crate) fn report(
        &mut self,
        unit: u32,
        kind: DiagKind,
        span: Span,
        node: Option<hir_lang::NodeRef>,
    ) {
        let unit = self
            .units
            .get(unit as usize)
            .map_or(UnitId::new(0), |u| u.id);
        self.diags.push(Diagnostic {
            kind,
            unit,
            span,
            node,
        });
    }
}

/// Orders table entries by (namespace, name).
pub(crate) fn entry_order(a: &Entry, b: &Entry) -> Ordering {
    (a.ns, a.name).cmp(&(b.ns, b.name))
}

/// Test fixtures: run phases 1 and 2 over one unit to inspect the model.
#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
pub(crate) mod fixture {
    use alloc::vec::Vec;

    use hir_lang::{Builder, Hir, ItemId, Name};
    use intern_lang::Interner;

    use super::{Model, Unit};
    use crate::{
        collect::{Bases, collect},
        env::NoEnv,
        policy::Policy,
        suggest::Suggester,
    };

    pub(crate) struct Fixture {
        pub(crate) names: Interner,
        pub(crate) b: Builder,
    }

    impl Fixture {
        pub(crate) fn new() -> Self {
            Self {
                names: Interner::new(),
                b: Builder::new(),
            }
        }

        pub(crate) fn name(&mut self, s: &str) -> Name {
            Name::new(self.names.intern(s))
        }

        /// Finishes the unit rooted at `root`, leaving a fresh builder.
        pub(crate) fn finish(&mut self, root: ItemId) -> Hir {
            core::mem::replace(&mut self.b, Builder::new())
                .finish(root)
                .expect("valid HIR")
        }
    }

    /// A model of one finished unit after collection and import resolution.
    pub(crate) fn model(hir: Hir, names: &Interner, policy: Policy) -> Model<'static> {
        let mut m = Model {
            policy,
            env: &NoEnv,
            units: Vec::new(),
            unit_ix: alloc::vec![(hir.unit(), 0)],
            roots: Vec::new(),
            scopes: Vec::new(),
            bindings: Vec::new(),
            imports: Vec::new(),
            sums: Vec::new(),
            diags: Vec::new(),
        };
        let c = collect(
            &hir,
            &m.policy,
            Bases {
                unit: 0,
                scope: 0,
                binding: 0,
                import: 0,
                sum: 0,
            },
        );
        m.scopes = c.scopes;
        m.bindings = c.bindings;
        m.imports = c.imports;
        m.sums = c.sums;
        m.units.push(Unit {
            id: hir.unit(),
            name: None,
            package: 0,
            hir,
            root_scope: c.root_scope,
            item_scope: c.item_scope,
            block_scope: c.block_scope,
            sum_table: c.sum_table,
            import_of: c.import_of,
            after_decl: Vec::new(),
        });
        for (kind, span, node) in c.diags {
            m.report(0, kind, span, Some(node));
        }
        let mut sugg = Suggester::new(u64::MAX);
        crate::imports::resolve_imports(&mut m, names, &mut sugg, u64::MAX).unwrap();
        m
    }

    /// The table scope of a module or class item.
    pub(crate) fn scope(m: &Model<'_>, item: ItemId) -> u32 {
        m.units[0].item_scope[item.index()]
    }

    /// Phases 1 to 3 over one unit: the model and the walk's output.
    pub(crate) fn walked(
        hir: Hir,
        names: &Interner,
        policy: Policy,
    ) -> (Model<'static>, Vec<crate::pass::UnitOut>) {
        let m = model(hir, names, policy);
        let mut sugg = Suggester::new(u64::MAX);
        let out = crate::pass::Pass::new(&m, names, &mut sugg, 0)
            .expect("unit 0")
            .run();
        (m, alloc::vec![out])
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use hir_lang::Vis;

    use super::{fixture::*, *};
    use crate::policy::Policy;

    /// mod outer { mod inner {} }  mod sibling {}
    fn nested() -> (Model<'static>, [u32; 4]) {
        let mut f = Fixture::new();
        let (inner_n, outer_n, sib_n) = (f.name("inner"), f.name("outer"), f.name("sibling"));
        let inner = f.b.module(Some(inner_n), &[]);
        let outer = f.b.module(Some(outer_n), &[inner]);
        let sibling = f.b.module(Some(sib_n), &[]);
        let root = f.b.module(None, &[outer, sibling]);
        let hir = f.b.finish(root).unwrap();
        let m = model(hir, &f.names, Policy::new());
        let s = [
            scope(&m, root),
            scope(&m, outer),
            scope(&m, inner),
            scope(&m, sibling),
        ];
        (m, s)
    }

    #[test]
    fn test_within_follows_module_nesting() {
        let (m, [root, outer, inner, sibling]) = nested();
        assert!(m.within(inner, outer));
        assert!(m.within(inner, root));
        assert!(m.within(outer, outer));
        assert!(!m.within(outer, inner));
        assert!(!m.within(sibling, outer));
        assert!(!m.within(NONE, root));
    }

    #[test]
    fn test_accessible_private_rules() {
        let (m, [root, outer, inner, sibling]) = nested();
        assert!(m.accessible(Vis::Private, outer, outer));
        assert!(m.accessible(Vis::Private, outer, inner));
        assert!(!m.accessible(Vis::Private, outer, sibling));
        assert!(!m.accessible(Vis::Private, inner, outer));
        assert!(m.accessible(Vis::Public, inner, root));
        assert!(m.accessible(Vis::Package, inner, sibling));
        // Protected outside classes behaves as private.
        assert!(!m.accessible(Vis::Protected, inner, root));
    }

    #[test]
    fn test_find_falls_back_to_failed_import_entry() {
        let mut f = Fixture::new();
        let (x, nowhere) = (f.name("x"), f.name("nowhere"));
        let segs = [
            hir_lang::Segment::new(nowhere, f.b.origin()),
            hir_lang::Segment::new(x, f.b.origin()),
        ];
        let segs = f.b.list(&segs);
        let path = f.b.path(hir_lang::Path::new(segs, hir_lang::Ns::Import));
        let imp = f.b.item(hir_lang::Item::new(
            None,
            hir_lang::ItemKind::Import { path, glob: false },
        ));
        let root = f.b.module(None, &[imp]);
        let hir = f.b.finish(root).unwrap();
        let m = model(hir, &f.names, Policy::new());
        let s = scope(&m, root);
        assert!(matches!(m.find(s, 0, x), Some(EntryState::Failed(_))));
        assert!(matches!(m.find(s, 1, x), Some(EntryState::Failed(_))));
        assert_eq!(m.find(s, 0, nowhere), None);
        assert_eq!(m.diags.len(), 1);
    }

    #[test]
    fn test_ix_saturates() {
        assert_eq!(ix(5), 5);
        assert_eq!(ix(usize::MAX), NONE);
    }
}
