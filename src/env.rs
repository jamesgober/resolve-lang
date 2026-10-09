//! The host environment: names that live outside the units being resolved.
//!
//! A [`Program`](crate::Program) resolves its units against each other. Every
//! other name (other packages, precompiled units, the standard library,
//! primitive types, host functions) comes from an [`Env`] the host provides.

use alloc::{collections::BTreeMap, vec::Vec};

use hir_lang::{DefId, ItemKind, Name, Ns, Res, Shape, Symbol, Vis};

use crate::policy::Namespace;

/// What kind of definition a resolution names, as far as scoping cares.
///
/// It decides which syntactic namespaces may name the definition (the table
/// of HIR spec §3.3), whether a path may continue through it (`Vec::new`),
/// and whether a bare identifier pattern matches it rather than binding.
///
/// # Examples
///
/// ```
/// use hir_lang::Ns;
/// use resolve_lang::DefKind;
///
/// assert!(DefKind::Fn.fits(Ns::Value));
/// assert!(!DefKind::Fn.fits(Ns::Type));
/// assert!(DefKind::Record { unit: false }.is_prefix());
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum DefKind {
    /// A module (or a whole unit's root module).
    Module,
    /// A function.
    Fn,
    /// A constant.
    Const,
    /// A global variable.
    Global,
    /// A record; `unit` for a record with no fields (`struct Unit;`).
    Record {
        /// The record has the unit shape.
        unit: bool,
    },
    /// A sum.
    Sum,
    /// A class; `mixin` for a PHP trait.
    Class {
        /// The class is a mixin (never instantiated).
        mixin: bool,
    },
    /// An interface.
    Interface,
    /// A type alias.
    Alias,
    /// An associated type.
    AssocType,
    /// A sum variant; `unit` for a variant with no fields.
    Variant {
        /// The variant has the unit shape.
        unit: bool,
    },
    /// A host or standard-library symbol.
    Extern,
    /// A primitive type.
    Prim,
    /// A local binder (a variable, parameter, or generic parameter). Paths
    /// name binders through `Res::Local`; this kind appears in diagnostics.
    Local,
    /// An error item (already reported).
    Err,
}

impl DefKind {
    /// The kind of a HIR item, or `None` for items that name nothing
    /// resolvable (`impl`, imports, mixin uses).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{ItemKind, RecordDef, Shape};
    /// use resolve_lang::DefKind;
    ///
    /// let unit = ItemKind::Record(RecordDef { shape: Shape::Unit, ..RecordDef::default() });
    /// assert_eq!(DefKind::of_item(&unit), Some(DefKind::Record { unit: true }));
    /// ```
    #[must_use]
    pub const fn of_item(kind: &ItemKind) -> Option<Self> {
        Some(match kind {
            ItemKind::Fn(_) => Self::Fn,
            ItemKind::Record(r) => Self::Record {
                unit: matches!(r.shape, Shape::Unit),
            },
            ItemKind::Sum(_) => Self::Sum,
            ItemKind::Class(c) => Self::Class { mixin: c.mixin },
            ItemKind::Interface(_) => Self::Interface,
            ItemKind::Alias { .. } => Self::Alias,
            ItemKind::AssocType { .. } => Self::AssocType,
            ItemKind::Const { .. } => Self::Const,
            ItemKind::Global { .. } => Self::Global,
            ItemKind::Module { .. } => Self::Module,
            ItemKind::Err => Self::Err,
            ItemKind::Impl(_) | ItemKind::Import { .. } | ItemKind::MixinUse(_) => return None,
        })
    }

    /// Whether a fully resolved path in syntactic namespace `ns` may name a
    /// definition of this kind (HIR spec §3.3).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Ns;
    /// use resolve_lang::DefKind;
    ///
    /// assert!(DefKind::Variant { unit: true }.fits(Ns::Pattern));
    /// assert!(DefKind::Module.fits(Ns::Import));
    /// assert!(!DefKind::Module.fits(Ns::Value));
    /// assert!(DefKind::Prim.fits(Ns::Type));
    /// ```
    #[must_use]
    pub const fn fits(self, ns: Ns) -> bool {
        match ns {
            Ns::Value => matches!(
                self,
                Self::Fn
                    | Self::Const
                    | Self::Global
                    | Self::Record { .. }
                    | Self::Class { .. }
                    | Self::Err
                    | Self::Variant { .. }
                    | Self::Extern
            ),
            Ns::Type => matches!(
                self,
                Self::Record { .. }
                    | Self::Sum
                    | Self::Class { .. }
                    | Self::Interface
                    | Self::Alias
                    | Self::AssocType
                    | Self::Err
                    | Self::Variant { .. }
                    | Self::Prim
                    | Self::Extern
            ),
            Ns::Pattern => matches!(
                self,
                Self::Const
                    | Self::Record { .. }
                    | Self::Class { .. }
                    | Self::Err
                    | Self::Variant { .. }
                    | Self::Extern
            ),
            Ns::Region => false,
            Ns::Import => !matches!(self, Self::Prim),
        }
    }

    /// Whether a path may continue past a definition of this kind, leaving the
    /// rest to type-directed or module resolution (a resolved *prefix*).
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::DefKind;
    ///
    /// assert!(DefKind::Sum.is_prefix());
    /// assert!(!DefKind::Fn.is_prefix());
    /// assert!(!DefKind::Variant { unit: false }.is_prefix());
    /// ```
    #[must_use]
    pub const fn is_prefix(self) -> bool {
        matches!(
            self,
            Self::Module
                | Self::Record { .. }
                | Self::Sum
                | Self::Class { .. }
                | Self::Interface
                | Self::Alias
                | Self::AssocType
                | Self::Err
                | Self::Prim
                | Self::Extern
        )
    }

    /// Whether a bare identifier pattern naming this definition matches it
    /// (a constant, a unit variant, a unit record) instead of binding.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::DefKind;
    ///
    /// assert!(DefKind::Const.is_pattern_constant());
    /// assert!(!DefKind::Variant { unit: false }.is_pattern_constant());
    /// ```
    #[must_use]
    pub const fn is_pattern_constant(self) -> bool {
        matches!(
            self,
            Self::Const | Self::Variant { unit: true } | Self::Record { unit: true }
        )
    }

    /// A short lowercase name, for messages.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::DefKind;
    ///
    /// assert_eq!(DefKind::Fn.name(), "function");
    /// ```
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Module => "module",
            Self::Fn => "function",
            Self::Const => "constant",
            Self::Global => "global",
            Self::Record { .. } => "record",
            Self::Sum => "sum type",
            Self::Class { mixin: false } => "class",
            Self::Class { mixin: true } => "mixin",
            Self::Interface => "interface",
            Self::Alias => "type alias",
            Self::AssocType => "associated type",
            Self::Variant { .. } => "variant",
            Self::Extern => "extern",
            Self::Prim => "primitive type",
            Self::Local => "local",
            Self::Err => "error item",
        }
    }
}

/// A name the environment exports: what it resolves to, its kind, and who may
/// see it.
///
/// # Examples
///
/// ```
/// use hir_lang::{Prim, Res, Vis};
/// use resolve_lang::{DefKind, Export};
///
/// let int = Export::new(Res::Prim(Prim::I64), DefKind::Prim);
/// assert_eq!(int.vis, Vis::Public);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Export {
    /// The resolution a path naming it gets.
    pub res: Res,
    /// Its kind.
    pub kind: DefKind,
    /// Its visibility. The environment filters what a unit may see; anything
    /// but `Public` is reported as an access error from another unit.
    pub vis: Vis,
}

impl Export {
    /// A public export.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Res, Symbol};
    /// use resolve_lang::{DefKind, Export};
    ///
    /// let sym = Symbol::from_u32(1).unwrap();
    /// let e = Export::new(Res::Extern(sym), DefKind::Extern);
    /// assert_eq!(e.kind, DefKind::Extern);
    /// ```
    #[must_use]
    pub const fn new(res: Res, kind: DefKind) -> Self {
        Self {
            res,
            kind,
            vis: Vis::Public,
        }
    }

    /// The same export with visibility `vis`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Res, Symbol, Vis};
    /// use resolve_lang::{DefKind, Export};
    ///
    /// let sym = Symbol::from_u32(1).unwrap();
    /// let e = Export::new(Res::Extern(sym), DefKind::Extern).with_vis(Vis::Package);
    /// assert_eq!(e.vis, Vis::Package);
    /// ```
    #[must_use]
    pub const fn with_vis(mut self, vis: Vis) -> Self {
        self.vis = vis;
        self
    }
}

/// The host's side of resolution: everything outside the program.
///
/// Every method has a default that knows nothing, so a host implements only
/// what its language has. Lookups are by exact [`Name`] (symbol and hygiene
/// mark). The resolver calls each method a bounded number of times per path
/// segment, and the enumeration methods only for glob imports from outside
/// the program and for did-you-mean suggestions.
///
/// # Examples
///
/// ```
/// use hir_lang::{Name, Prim, Res};
/// use resolve_lang::{DefKind, Env, Export, Namespace};
///
/// /// Primitive types only: `int` is `i64`.
/// struct Prims { int: Name }
///
/// impl Env for Prims {
///     fn prelude(&self, name: Name, ns: Namespace) -> Option<Export> {
///         (name == self.int && ns == Namespace::Type)
///             .then(|| Export::new(Res::Prim(Prim::I64), DefKind::Prim))
///     }
/// }
/// # let _ = Prims { int: Name::new(hir_lang::Symbol::from_u32(1).unwrap()) };
/// ```
pub trait Env {
    /// A name visible as the first segment of a path in every unit, after
    /// every lexical scope: another package, a precompiled unit, an extern
    /// module. Usually a [`DefKind::Module`] or [`DefKind::Extern`].
    fn root(&self, name: Name) -> Option<Export> {
        let _ = name;
        None
    }

    /// The prelude: names visible everywhere, after lexical scopes and roots
    /// (builtins, primitive type names).
    fn prelude(&self, name: Name, ns: Namespace) -> Option<Export> {
        let _ = (name, ns);
        None
    }

    /// A member of a container the program does not define: a module or class
    /// of another package, an extern module. `container` is the resolution
    /// the path reached so far.
    fn member(&self, container: Res, name: Name, ns: Namespace) -> Option<Export> {
        let _ = (container, name, ns);
        None
    }

    /// Calls `f` for every member of an outside container, for glob imports
    /// and suggestions.
    fn for_each_member(&self, container: Res, f: &mut dyn FnMut(Name, Namespace, Export)) {
        let _ = (container, f);
    }

    /// Calls `f` for every root name, for suggestions.
    fn for_each_root(&self, f: &mut dyn FnMut(Name)) {
        let _ = f;
    }

    /// Calls `f` for every prelude name, for suggestions.
    fn for_each_prelude(&self, f: &mut dyn FnMut(Name, Namespace)) {
        let _ = f;
    }
}

/// An environment with nothing in it: every name outside the program is
/// unresolved.
///
/// # Examples
///
/// ```
/// use hir_lang::{Name, Symbol};
/// use resolve_lang::{Env, NoEnv};
///
/// let n = Name::new(Symbol::from_u32(1).unwrap());
/// assert!(NoEnv.root(n).is_none());
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NoEnv;

impl Env for NoEnv {}

/// A container key for [`MapEnv`]: a definition or an extern symbol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ContainerKey {
    Def(DefId),
    Extern(Symbol),
}

impl ContainerKey {
    fn of(res: Res) -> Option<Self> {
        match res {
            Res::Def(d) => Some(Self::Def(d)),
            Res::Extern(s) => Some(Self::Extern(s)),
            _ => None,
        }
    }
}

/// A ready-made in-memory [`Env`]: roots, a prelude, and members of outside
/// containers, each registered once.
///
/// Lookups are `O(log n)`; enumeration is in name order, so suggestions are
/// deterministic.
///
/// # Examples
///
/// ```
/// use hir_lang::{Name, Prim, Res};
/// use intern_lang::Interner;
/// use resolve_lang::{DefKind, Env, Export, MapEnv, Namespace};
///
/// let mut names = Interner::new();
/// let int = Name::new(names.intern("int"));
/// let env = MapEnv::new().with_prelude(int, Namespace::Type, Export::new(Res::Prim(Prim::I64), DefKind::Prim));
/// assert_eq!(env.prelude(int, Namespace::Type).map(|e| e.res), Some(Res::Prim(Prim::I64)));
/// assert!(env.prelude(int, Namespace::Value).is_none());
/// ```
#[derive(Clone, Debug, Default)]
pub struct MapEnv {
    roots: BTreeMap<Name, Export>,
    prelude: BTreeMap<(Name, Namespace), Export>,
    members: BTreeMap<ContainerKey, BTreeMap<(Name, Namespace), Export>>,
}

impl MapEnv {
    /// An empty environment.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::MapEnv;
    ///
    /// let _env = MapEnv::new();
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a root name (replacing an earlier one of the same name).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Name, Res};
    /// use intern_lang::Interner;
    /// use resolve_lang::{DefKind, Env, Export, MapEnv};
    ///
    /// let mut names = Interner::new();
    /// let std = names.intern("std");
    /// let env = MapEnv::new().with_root(Name::new(std), Export::new(Res::Extern(std), DefKind::Extern));
    /// assert!(env.root(Name::new(std)).is_some());
    /// ```
    #[must_use]
    pub fn with_root(mut self, name: Name, export: Export) -> Self {
        let _replaced = self.roots.insert(name, export);
        self
    }

    /// Adds a prelude name in one namespace.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Name, Res};
    /// use intern_lang::Interner;
    /// use resolve_lang::{DefKind, Env, Export, MapEnv, Namespace};
    ///
    /// let mut names = Interner::new();
    /// let print = names.intern("print");
    /// let env = MapEnv::new().with_prelude(Name::new(print), Namespace::Value, Export::new(Res::Extern(print), DefKind::Extern));
    /// assert!(env.prelude(Name::new(print), Namespace::Value).is_some());
    /// ```
    #[must_use]
    pub fn with_prelude(mut self, name: Name, ns: Namespace, export: Export) -> Self {
        let _replaced = self.prelude.insert((name, ns), export);
        self
    }

    /// Adds a member of an outside container (a `Res::Def` or `Res::Extern`;
    /// other resolutions are ignored).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Name, Res};
    /// use intern_lang::Interner;
    /// use resolve_lang::{DefKind, Env, Export, MapEnv, Namespace};
    ///
    /// let mut names = Interner::new();
    /// let (os, path) = (names.intern("os"), names.intern("path"));
    /// let env = MapEnv::new().with_member(Res::Extern(os), Name::new(path), Namespace::Module, Export::new(Res::Extern(path), DefKind::Extern));
    /// assert!(env.member(Res::Extern(os), Name::new(path), Namespace::Module).is_some());
    /// ```
    #[must_use]
    pub fn with_member(
        mut self,
        container: Res,
        name: Name,
        ns: Namespace,
        export: Export,
    ) -> Self {
        if let Some(key) = ContainerKey::of(container) {
            let _replaced = self
                .members
                .entry(key)
                .or_default()
                .insert((name, ns), export);
        }
        self
    }
}

impl Env for MapEnv {
    fn root(&self, name: Name) -> Option<Export> {
        self.roots.get(&name).copied()
    }

    fn prelude(&self, name: Name, ns: Namespace) -> Option<Export> {
        self.prelude.get(&(name, ns)).copied()
    }

    fn member(&self, container: Res, name: Name, ns: Namespace) -> Option<Export> {
        let key = ContainerKey::of(container)?;
        self.members.get(&key)?.get(&(name, ns)).copied()
    }

    fn for_each_member(&self, container: Res, f: &mut dyn FnMut(Name, Namespace, Export)) {
        let Some(members) = ContainerKey::of(container).and_then(|k| self.members.get(&k)) else {
            return;
        };
        for (&(name, ns), export) in members {
            f(name, ns, *export);
        }
    }

    fn for_each_root(&self, f: &mut dyn FnMut(Name)) {
        for name in self.roots.keys() {
            f(*name);
        }
    }

    fn for_each_prelude(&self, f: &mut dyn FnMut(Name, Namespace)) {
        for (name, ns) in self.prelude.keys() {
            f(*name, *ns);
        }
    }
}

/// Collects an environment's member names of one container, sorted.
pub(crate) fn env_members(env: &dyn Env, container: Res) -> Vec<(Name, Namespace, Export)> {
    let mut out = Vec::new();
    env.for_each_member(container, &mut |n, ns, e| out.push((n, ns, e)));
    out
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;
    use hir_lang::{Def, ItemId, Prim, UnitId};

    fn sym(i: u32) -> Symbol {
        Symbol::from_u32(i).unwrap()
    }

    #[test]
    fn test_map_env_enumerates_members_of_one_container_only() {
        let a = Res::Extern(sym(1));
        let b = Res::Extern(sym(2));
        let e = Export::new(Res::Extern(sym(9)), DefKind::Extern);
        let env = MapEnv::new()
            .with_member(a, Name::new(sym(5)), Namespace::Value, e)
            .with_member(a, Name::new(sym(3)), Namespace::Type, e)
            .with_member(b, Name::new(sym(4)), Namespace::Value, e);
        let names: Vec<u32> = env_members(&env, a)
            .iter()
            .map(|(n, _, _)| n.sym.as_u32())
            .collect();
        assert_eq!(names, [3, 5]);
        assert!(env_members(&env, Res::Prim(Prim::I32)).is_empty());
    }

    #[test]
    fn test_def_kind_matches_hir_namespace_table() {
        assert!(DefKind::Class { mixin: false }.fits(Ns::Pattern));
        assert!(!DefKind::Sum.fits(Ns::Value));
        assert!(!DefKind::Fn.fits(Ns::Region));
        assert!(DefKind::Extern.fits(Ns::Import));
        assert!(!DefKind::Prim.fits(Ns::Import));
    }

    #[test]
    fn test_member_on_non_container_is_ignored() {
        let d = DefId::foreign(UnitId::new(1), Def::Item(ItemId::from_index(0).unwrap()));
        let n = Name::new(sym(1));
        let env = MapEnv::new().with_member(
            Res::Err,
            n,
            Namespace::Value,
            Export::new(Res::Def(d), DefKind::Fn),
        );
        assert!(env.member(Res::Err, n, Namespace::Value).is_none());
        let env = env.with_member(
            Res::Def(d),
            n,
            Namespace::Value,
            Export::new(Res::Def(d), DefKind::Fn),
        );
        assert!(env.member(Res::Def(d), n, Namespace::Value).is_some());
    }
}
