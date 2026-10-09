//! The program-wide data every phase shares: units, scope tables, bindings,
//! imports. All indexes are dense `u32`s into vectors; `NONE` marks absence.

use alloc::{collections::BTreeMap, string::String, vec::Vec};
use core::cmp::Ordering;

use hir_lang::{Def, DefId, Hir, ItemId, Name, PathId, Res, Span, Symbol, UnitId, VariantId, Vis};
use intern_lang::Lookup;

use crate::{
    diag::{DiagKind, Diagnostic},
    env::{DefKind, Env},
    policy::{Hoist, Namespace, Policy},
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

/// Case folding of names, for the tables a policy makes case-insensitive.
///
/// Folding maps every symbol to the canonical symbol of its ASCII case class:
/// the symbol spelled in lowercase when the interner has it, otherwise the
/// lowest-numbered symbol with the same lowercase spelling. Both are fixed
/// by the interner alone, so the mapping is deterministic and does not depend
/// on the order units or names are visited in. Tables then compare folded
/// names, and every record keeps its written name for messages and the index.
pub(crate) struct Fold {
    /// By symbol id: the canonical symbol's id, or 0 for the symbol itself.
    /// Empty when no table folds.
    map: Vec<u32>,
    /// Bit `t` set when table `t` folds.
    tables: u8,
}

impl Fold {
    /// No folding: every name is its own key.
    pub(crate) const fn none() -> Self {
        Self {
            map: Vec::new(),
            tables: 0,
        }
    }

    /// The fold for `policy` over every symbol of `names`. Free when no table
    /// folds; otherwise one pass over the interner, allocating only for
    /// symbols that contain an ASCII capital.
    pub(crate) fn build<L: Lookup>(policy: &Policy, names: &L) -> Self {
        if !policy.any_folds() {
            return Self::none();
        }
        let mut tables = 0u8;
        for t in 0..crate::policy::TABLES {
            if policy.table_folds(ix(t) as u8) {
                tables |= 1 << t;
            }
        }
        let n = names.len();
        let mut map = alloc::vec![0u32; n.saturating_add(1)];
        // Lowercase spellings that are not interned themselves: the first
        // (lowest-numbered) symbol with that spelling stands for all.
        let mut first: BTreeMap<String, u32> = BTreeMap::new();
        for id in 1..=ix(n) {
            let Some(sym) = Symbol::from_u32(id) else {
                continue;
            };
            let lower = names
                .resolve_with(sym, |s: &str| {
                    s.bytes()
                        .any(|b| b.is_ascii_uppercase())
                        .then(|| s.to_ascii_lowercase())
                })
                .flatten();
            let Some(lower) = lower else { continue };
            let canon = match names.get(&lower) {
                Some(c) => c.as_u32(),
                None => *first.entry(lower).or_insert(id),
            };
            if canon != id {
                if let Some(slot) = map.get_mut(id as usize) {
                    *slot = canon;
                }
            }
        }
        Self { map, tables }
    }

    /// The canonical symbol of `sym`'s case class (itself without folding,
    /// and for a symbol the interner did not have when the fold was built).
    #[inline]
    pub(crate) fn sym(&self, sym: Symbol) -> Symbol {
        match self.map.get(sym.as_u32() as usize) {
            Some(&c) if c != 0 => Symbol::from_u32(c).unwrap_or(sym),
            _ => sym,
        }
    }

    /// `name` folded regardless of table: the key that groups every spelling
    /// that some table could treat as equal (identity without folding).
    #[inline]
    pub(crate) fn name(&self, name: Name) -> Name {
        if self.tables == 0 {
            return name;
        }
        Name {
            sym: self.sym(name.sym),
            mark: name.mark,
        }
    }

    /// The key of `name` in table `t`: folded if that table folds.
    #[inline]
    pub(crate) fn key(&self, t: u8, name: Name) -> Name {
        if t == ANY_NS {
            return self.name(name);
        }
        if t < 8 && self.tables & (1 << t) != 0 {
            Name {
                sym: self.sym(name.sym),
                mark: name.mark,
            }
        } else {
            name
        }
    }

    /// The key of `name` in the table of namespace `ns`.
    pub(crate) fn key_ns(&self, policy: &Policy, ns: Namespace, name: Name) -> Name {
        self.key(policy.table_ix(ns), name)
    }
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
    /// The name as written (messages, suggestions, members).
    pub(crate) name: Name,
    /// The name as the table compares it (`Fold::key(ns, name)`).
    pub(crate) key: Name,
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
    /// The table key (folded per the table's case).
    pub(crate) name: Name,
    /// A spelling as written, for suggestions.
    pub(crate) spelling: Name,
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
    pub(crate) fold: Fold,
    pub(crate) env: &'e dyn Env,
    pub(crate) units: Vec<Unit>,
    /// (unit id, unit index), sorted, for `DefId` lookups.
    pub(crate) unit_ix: Vec<(UnitId, u32)>,
    /// (root name key in the module table, unit index), sorted.
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

    /// Looks a name up in a finished table (by its key in table `ns`): the
    /// exact namespace, else a failed import of that name.
    pub(crate) fn find(&self, scope: u32, ns: u8, name: Name) -> Option<EntryState> {
        let table = &self.scopes.get(scope as usize)?.table;
        let k = self.fold.key(ns, name);
        let key = |e: &Entry| (e.ns, e.name).cmp(&(ns, k));
        if let Ok(i) = table.binary_search_by(key) {
            return table.get(i).map(|e| e.state);
        }
        let k = self.fold.name(name);
        let any = |e: &Entry| (e.ns, e.name).cmp(&(ANY_NS, k));
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

    /// The unit index of the root named `name`, if a program unit claims it.
    pub(crate) fn root_unit(&self, name: Name) -> Option<u32> {
        let key = self.fold.key_ns(&self.policy, Namespace::Module, name);
        let i = self.roots.binary_search_by(|(n, _)| n.cmp(&key)).ok()?;
        self.roots.get(i).map(|(_, u)| *u)
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
            fold: super::Fold::build(&policy, names),
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
            &m.fold,
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
    fn test_fold_is_canonical_and_order_free() {
        let mut names = intern_lang::Interner::new();
        let up = names.intern("FOO");
        let mixed = names.intern("Foo");
        let other = names.intern("Bar");
        let fold = Fold::build(&Policy::php(), &names);
        // No lowercase spelling interned: the lowest-numbered variant wins.
        assert_eq!(fold.sym(mixed), up);
        assert_eq!(fold.sym(up), up);
        assert_eq!(fold.sym(other), other);
        let low = names.intern("foo");
        let fold = Fold::build(&Policy::php(), &names);
        assert_eq!(fold.sym(up), low);
        assert_eq!(fold.sym(mixed), low);
        // The constant table keeps case; the value table folds.
        let t_const = Policy::php().table_ix(Namespace::Const);
        let t_value = Policy::php().table_ix(Namespace::Value);
        assert_eq!(fold.key(t_const, Name::new(up)).sym, up);
        assert_eq!(fold.key(t_value, Name::new(up)).sym, low);
        // Non-ASCII bytes never fold.
        let e1 = names.intern("\u{c9}t\u{e9}");
        let e2 = names.intern("\u{e9}t\u{e9}");
        let fold = Fold::build(&Policy::php(), &names);
        assert_ne!(fold.sym(e1), fold.sym(e2));
        // Without a folding table, folding is the identity.
        let none = Fold::build(&Policy::new(), &names);
        assert_eq!(none.name(Name::new(up)).sym, up);
    }

    #[test]
    fn test_ix_saturates() {
        assert_eq!(ix(5), 5);
        assert_eq!(ix(usize::MAX), NONE);
    }
}
