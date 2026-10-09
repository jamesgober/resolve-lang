//! The scoping policy: how one language binds names, as data.
//!
//! Every forged language reaches resolve-lang as HIR, so the differences
//! between, say, PHP, Python, and Kraken are not separate resolvers but
//! settings: when an item becomes visible (hoisting), whether a binder may
//! reuse a visible name (shadowing), which namespaces exist and which share a
//! table (merging), what a method body can see of its class, how the
//! late-static-binding roots bind, and how imports and visibility behave.

use hir_lang::{ItemKind, Vis};

/// One of the language-level namespaces a name can live in.
///
/// HIR paths carry a syntactic namespace ([`hir_lang::Ns`]); these are the
/// *tables* names are stored in. A language merges tables with
/// [`Policy::with_merge`] (Python keeps everything in one table; Rust keeps types
/// and modules in one).
///
/// # Examples
///
/// ```
/// use resolve_lang::Namespace;
///
/// assert_eq!(Namespace::Value.name(), "value");
/// assert_eq!(Namespace::ALL.len(), 5);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Namespace {
    /// Functions, constants, globals, constructors.
    Value,
    /// Records, sums, classes, interfaces, aliases.
    Type,
    /// Modules and units.
    Module,
    /// Macros. HIR has no macro items (macros expand before lowering); hosts
    /// may still export names here through [`Env`](crate::Env).
    Macro,
    /// Loop and block labels. Labels are binders resolved by lowering, so no
    /// HIR path is looked up here; the namespace exists for merging rules.
    Label,
}

impl Namespace {
    /// Every namespace, in table order.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Namespace;
    ///
    /// assert_eq!(Namespace::ALL[0], Namespace::Value);
    /// ```
    pub const ALL: [Self; 5] = [
        Self::Value,
        Self::Type,
        Self::Module,
        Self::Macro,
        Self::Label,
    ];

    /// The lowercase name, for messages.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Namespace;
    ///
    /// assert_eq!(Namespace::Module.name(), "module");
    /// ```
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Value => "value",
            Self::Type => "type",
            Self::Module => "module",
            Self::Macro => "macro",
            Self::Label => "label",
        }
    }

    #[inline]
    pub(crate) const fn index(self) -> usize {
        self as usize
    }

    pub(crate) const fn from_index(i: usize) -> Self {
        match i {
            0 => Self::Value,
            1 => Self::Type,
            2 => Self::Module,
            3 => Self::Macro,
            _ => Self::Label,
        }
    }
}

/// A set of [`Namespace`]s, as a bit set.
///
/// # Examples
///
/// ```
/// use resolve_lang::{Namespace, NsSet};
///
/// let set = NsSet::of(&[Namespace::Type, Namespace::Value]);
/// assert!(set.contains(Namespace::Type));
/// assert!(!set.contains(Namespace::Module));
/// assert_eq!(set.iter().count(), 2);
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct NsSet(u8);

impl NsSet {
    /// The empty set.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::NsSet;
    ///
    /// assert!(NsSet::EMPTY.is_empty());
    /// ```
    pub const EMPTY: Self = Self(0);

    /// A set holding exactly `namespaces`.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Namespace, NsSet};
    ///
    /// assert_eq!(NsSet::of(&[Namespace::Value]), NsSet::single(Namespace::Value));
    /// ```
    #[must_use]
    pub const fn of(namespaces: &[Namespace]) -> Self {
        let mut bits = 0u8;
        let mut i = 0;
        while i < namespaces.len() {
            bits |= 1 << namespaces[i] as u8;
            i += 1;
        }
        Self(bits)
    }

    /// A set holding one namespace.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Namespace, NsSet};
    ///
    /// assert!(NsSet::single(Namespace::Macro).contains(Namespace::Macro));
    /// ```
    #[must_use]
    pub const fn single(ns: Namespace) -> Self {
        Self(1 << ns as u8)
    }

    /// Whether `ns` is in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Namespace, NsSet};
    ///
    /// assert!(!NsSet::EMPTY.contains(Namespace::Value));
    /// ```
    #[must_use]
    pub const fn contains(self, ns: Namespace) -> bool {
        self.0 & (1 << ns as u8) != 0
    }

    /// Whether the set is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Namespace, NsSet};
    ///
    /// assert!(!NsSet::single(Namespace::Type).is_empty());
    /// ```
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// The set with `ns` added.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Namespace, NsSet};
    ///
    /// let s = NsSet::EMPTY.with(Namespace::Type);
    /// assert!(s.contains(Namespace::Type));
    /// ```
    #[must_use]
    pub const fn with(self, ns: Namespace) -> Self {
        Self(self.0 | (1 << ns as u8))
    }

    /// The namespaces in the set, in table order.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Namespace, NsSet};
    ///
    /// let v: Vec<_> = NsSet::of(&[Namespace::Module, Namespace::Value]).iter().collect();
    /// assert_eq!(v, [Namespace::Value, Namespace::Module]);
    /// ```
    pub fn iter(self) -> impl Iterator<Item = Namespace> {
        Namespace::ALL
            .into_iter()
            .filter(move |ns| self.contains(*ns))
    }
}

/// The kinds of named items a policy distinguishes.
///
/// # Examples
///
/// ```
/// use resolve_lang::ItemClass;
///
/// assert_eq!(ItemClass::ALL.len(), 11);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ItemClass {
    /// A function or method.
    Fn,
    /// A record (struct).
    Record,
    /// A sum (enum).
    Sum,
    /// A class (or PHP trait, a mixin class).
    Class,
    /// An interface or trait.
    Interface,
    /// A type alias.
    Alias,
    /// An associated type.
    AssocType,
    /// A constant.
    Const,
    /// A global variable (a static, a Python module-level variable).
    Global,
    /// A module.
    Module,
    /// An import (`use`, `import`, `from … import`).
    Import,
}

impl ItemClass {
    /// Every item class.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::ItemClass;
    ///
    /// assert_eq!(ItemClass::ALL[0], ItemClass::Fn);
    /// ```
    pub const ALL: [Self; 11] = [
        Self::Fn,
        Self::Record,
        Self::Sum,
        Self::Class,
        Self::Interface,
        Self::Alias,
        Self::AssocType,
        Self::Const,
        Self::Global,
        Self::Module,
        Self::Import,
    ];

    /// The class of a HIR item kind, or `None` for kinds that bind no name
    /// (`impl`, mixin use, error items).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{FnDef, ItemKind};
    /// use resolve_lang::ItemClass;
    ///
    /// assert_eq!(ItemClass::of(&ItemKind::Fn(FnDef::default())), Some(ItemClass::Fn));
    /// assert_eq!(ItemClass::of(&ItemKind::Err), None);
    /// ```
    #[must_use]
    pub const fn of(kind: &ItemKind) -> Option<Self> {
        Some(match kind {
            ItemKind::Fn(_) => Self::Fn,
            ItemKind::Record(_) => Self::Record,
            ItemKind::Sum(_) => Self::Sum,
            ItemKind::Class(_) => Self::Class,
            ItemKind::Interface(_) => Self::Interface,
            ItemKind::Alias { .. } => Self::Alias,
            ItemKind::AssocType { .. } => Self::AssocType,
            ItemKind::Const { .. } => Self::Const,
            ItemKind::Global { .. } => Self::Global,
            ItemKind::Module { .. } => Self::Module,
            ItemKind::Import { .. } => Self::Import,
            ItemKind::Impl(_) | ItemKind::MixinUse(_) | ItemKind::Err => return None,
        })
    }

    #[inline]
    const fn index(self) -> usize {
        self as usize
    }
}

/// When an item's name becomes visible in its scope.
///
/// # Examples
///
/// ```
/// use resolve_lang::{Hoist, ItemClass, Policy};
///
/// // PHP: a function declared anywhere is visible in its whole namespace.
/// assert_eq!(Policy::php().hoisting(ItemClass::Fn), Hoist::Module);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Hoist {
    /// Visible throughout the scope that declares it, before and after the
    /// declaration (Rust and Kraken items, Python's per-scope binding rule).
    Scope,
    /// Visible from the declaration to the end of its scope, including inside
    /// itself, so a function can recurse (C-style declare-before-use).
    AfterDecl,
    /// Visible throughout the nearest enclosing module, wherever it is
    /// declared, even inside a function body or a conditional block (PHP
    /// functions and classes).
    Module,
}

/// Whether a binder may reuse a name that is already visible.
///
/// # Examples
///
/// ```
/// use resolve_lang::{Policy, Shadowing};
///
/// let p = Policy::new().with_shadowing(Shadowing::DenySameScope);
/// assert_eq!(p.shadowing(), Shadowing::DenySameScope);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Shadowing {
    /// Any binder may shadow any visible name (Rust `let`, Python, PHP).
    Allow,
    /// A binder may not reuse a name bound earlier in the *same* scope
    /// (JavaScript `let`, a parameter list with a repeated name).
    DenySameScope,
    /// A binder may not reuse the name of any local binder visible from the
    /// same frame (C#, Zig).
    DenyLocals,
}

/// What two definitions of one name in one scope and namespace mean.
///
/// # Examples
///
/// ```
/// use resolve_lang::{Policy, Redefinition};
///
/// assert_eq!(Policy::python().redefinition(), Redefinition::LastWins);
/// assert_eq!(Policy::kraken().redefinition(), Redefinition::Error);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Redefinition {
    /// A duplicate definition is an error; the first one is kept.
    Error,
    /// A later definition replaces an earlier one (Python `def f` twice).
    /// With [`Hoist::AfterDecl`] each definition is visible from its own
    /// declaration on.
    LastWins,
}

/// What code nested in a class can see of the class's members unqualified.
///
/// # Examples
///
/// ```
/// use resolve_lang::{ClassScope, Policy};
///
/// assert_eq!(Policy::python().class_scope(), ClassScope::BodyOnly);
/// assert_eq!(Policy::php().class_scope(), ClassScope::Qualified);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ClassScope {
    /// Members are in lexical scope everywhere inside the class, methods
    /// included (Java, C++, Kraken). Only the class's own members are seen
    /// unqualified; inherited members go through `self::`/type-directed
    /// lookup.
    Lexical,
    /// Members are visible to the class body's own initializers but not
    /// inside methods, lambdas, or nested classes (Python).
    BodyOnly,
    /// Members are never visible unqualified; code writes `self::x`,
    /// `static::x`, or `$this->x` (PHP).
    Qualified,
}

/// Whether a nested module sees the names of the modules around it.
///
/// # Examples
///
/// ```
/// use resolve_lang::{ModuleScope, Policy};
///
/// assert_eq!(Policy::kraken().module_scope(), ModuleScope::Isolated);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ModuleScope {
    /// A nested module starts a fresh lexical world: outer items are reached
    /// through `super::` or an import (Rust, Kraken).
    Isolated,
    /// A nested module sees enclosing scopes' names (PHP namespaces falling
    /// back outward, languages with lexically nested modules).
    Lexical,
}

/// How a type-relative root (`self::`, `parent::`, `static::`) binds.
///
/// # Examples
///
/// ```
/// use resolve_lang::{Policy, RootBinding};
///
/// // PHP: `static::` is late static binding, resolved at run time.
/// assert_eq!(Policy::php().static_root(), RootBinding::Late);
/// assert_eq!(Policy::php().self_root(), RootBinding::Early);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RootBinding {
    /// Bound at resolution time against the enclosing class (or its first
    /// base, for `parent::`): a member found there is resolved now; one not
    /// found is left to type-directed resolution.
    Early,
    /// Bound late (at run time or by the type checker): the whole path is
    /// left type-directed (`unresolved = segments`).
    Late,
    /// The language has no such root; a path using it is reported.
    Unsupported,
}

/// How an import's own visibility affects re-export.
///
/// # Examples
///
/// ```
/// use resolve_lang::{Policy, Reexport};
///
/// assert_eq!(Policy::python().reexport(), Reexport::Always);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Reexport {
    /// An import is visible to other modules exactly as its item's [`Vis`]
    /// says (`pub use` re-exports, plain `use` does not).
    AsDeclared,
    /// Every import becomes part of the module's exports (Python: an imported
    /// name is a module attribute).
    Always,
    /// Imports are never exported (PHP: `use` is file-local).
    Never,
}

/// A language's complete scoping policy.
///
/// Start from a preset ([`kraken`](Self::kraken), [`php`](Self::php),
/// [`python`](Self::python)) or [`new`](Self::new) (the lexical default, the
/// same as Kraken), then adjust with the `with_*` setters. The policy is plain
/// data, normally read from the language's sketch.
///
/// # Examples
///
/// ```
/// use resolve_lang::{ClassScope, Hoist, ItemClass, Namespace, Policy};
///
/// let p = Policy::new()
///     .with_hoisting(ItemClass::Fn, Hoist::AfterDecl)
///     .with_class_scope(ClassScope::BodyOnly)
///     .with_merge(Namespace::Type, Namespace::Value);
/// assert_eq!(p.hoisting(ItemClass::Fn), Hoist::AfterDecl);
/// assert_eq!(p.table(Namespace::Type), Namespace::Value);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Policy {
    hoist: [Hoist; 11],
    occupies: [NsSet; 11],
    merge: [Namespace; 5],
    shadowing: Shadowing,
    redefinition: Redefinition,
    class_scope: ClassScope,
    module_scope: ModuleScope,
    roots: [RootBinding; 3],
    enforce_visibility: bool,
    private_to_descendants: bool,
    globs: bool,
    aliases: bool,
    reexport: Reexport,
    implicit_globals: bool,
}

impl Default for Policy {
    fn default() -> Self {
        Self::new()
    }
}

impl Policy {
    /// The lexical default (equal to [`kraken`](Self::kraken)): every item
    /// hoisted to its scope; separate value, type, and macro tables with
    /// modules sharing the type table; class members visible in methods;
    /// isolated nested modules; `Self::` early, `parent::`/`static::`
    /// unsupported; visibility enforced with private items visible to child
    /// modules; globs, aliases, and declared re-exports.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{ItemClass, Namespace, NsSet, Policy};
    ///
    /// let p = Policy::new();
    /// assert_eq!(p.occupies(ItemClass::Record), NsSet::of(&[Namespace::Type, Namespace::Value]));
    /// assert!(p.visibility_enforced());
    /// ```
    #[must_use]
    pub const fn new() -> Self {
        use Namespace::{Label, Macro, Module, Type, Value};
        let value = NsSet::single(Value);
        let ty = NsSet::single(Type);
        let both = NsSet::of(&[Type, Value]);
        Self {
            hoist: [Hoist::Scope; 11],
            // Fn Record Sum Class Interface Alias AssocType Const Global Module Import
            occupies: [
                value,
                both,
                ty,
                both,
                ty,
                ty,
                ty,
                value,
                value,
                NsSet::single(Module),
                NsSet::EMPTY,
            ],
            merge: [Value, Type, Type, Macro, Label],
            shadowing: Shadowing::Allow,
            redefinition: Redefinition::Error,
            class_scope: ClassScope::Lexical,
            module_scope: ModuleScope::Isolated,
            roots: [
                RootBinding::Early,
                RootBinding::Unsupported,
                RootBinding::Unsupported,
            ],
            enforce_visibility: true,
            private_to_descendants: true,
            globs: true,
            aliases: true,
            reexport: Reexport::AsDeclared,
            implicit_globals: false,
        }
    }

    /// Kraken and Iron: lexical scoping, modules with imports and
    /// visibility. Equal to [`new`](Self::new).
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Policy;
    ///
    /// assert_eq!(Policy::kraken(), Policy::new());
    /// ```
    #[must_use]
    pub const fn kraken() -> Self {
        Self::new()
    }

    /// PHP (and Mox): functions, classes, interfaces, enums, and constants are
    /// visible in their whole namespace wherever declared; class members are
    /// reached only through `self::`/`parent::`/`static::` (late static
    /// binding for `static::`); `use` imports are file-local and have no
    /// globs; `global $x` may name a global that does not exist yet.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Hoist, ItemClass, Policy};
    ///
    /// let p = Policy::php();
    /// assert_eq!(p.hoisting(ItemClass::Class), Hoist::Module);
    /// assert!(!p.globs_allowed());
    /// assert!(p.implicit_globals());
    /// ```
    #[must_use]
    pub const fn php() -> Self {
        let mut p = Self::new();
        let mut i = 0;
        while i < 11 {
            let c = ItemClass::ALL[i];
            if matches!(
                c,
                ItemClass::Fn
                    | ItemClass::Record
                    | ItemClass::Sum
                    | ItemClass::Class
                    | ItemClass::Interface
                    | ItemClass::Const
            ) {
                p.hoist[i] = Hoist::Module;
            }
            i += 1;
        }
        p.class_scope = ClassScope::Qualified;
        p.module_scope = ModuleScope::Lexical;
        p.roots = [RootBinding::Early, RootBinding::Early, RootBinding::Late];
        p.globs = false;
        p.reexport = Reexport::Never;
        p.implicit_globals = true;
        p
    }

    /// Python (and Mercury): one table for every kind of name; a name bound
    /// anywhere in a scope belongs to the whole scope; class bodies are not
    /// visible to methods; redefinition rebinds; visibility is convention
    /// only; imports become module attributes.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Namespace, Policy};
    ///
    /// let p = Policy::python();
    /// assert_eq!(p.table(Namespace::Type), Namespace::Value);
    /// assert_eq!(p.table(Namespace::Module), Namespace::Value);
    /// assert!(!p.visibility_enforced());
    /// ```
    #[must_use]
    pub const fn python() -> Self {
        let mut p = Self::new();
        p.merge = [
            Namespace::Value,
            Namespace::Value,
            Namespace::Value,
            Namespace::Value,
            Namespace::Label,
        ];
        p.redefinition = Redefinition::LastWins;
        p.class_scope = ClassScope::BodyOnly;
        p.module_scope = ModuleScope::Lexical;
        p.roots = [RootBinding::Unsupported; 3];
        p.enforce_visibility = false;
        p.reexport = Reexport::Always;
        p.implicit_globals = true;
        p
    }

    // ------------------------------------------------------------ setters

    /// Sets when items of `class` become visible.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Hoist, ItemClass, Policy};
    ///
    /// let p = Policy::new().with_hoisting(ItemClass::Global, Hoist::AfterDecl);
    /// assert_eq!(p.hoisting(ItemClass::Global), Hoist::AfterDecl);
    /// ```
    #[must_use]
    pub const fn with_hoisting(mut self, class: ItemClass, hoist: Hoist) -> Self {
        self.hoist[class.index()] = hoist;
        self
    }

    /// Sets the namespaces items of `class` define their name in. Imports
    /// ignore this (an import binds whatever its target defines).
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{ItemClass, Namespace, NsSet, Policy};
    ///
    /// // Rust: a braced struct defines no constructor value.
    /// let p = Policy::new().with_occupies(ItemClass::Record, NsSet::single(Namespace::Type));
    /// assert!(!p.occupies(ItemClass::Record).contains(Namespace::Value));
    /// ```
    #[must_use]
    pub const fn with_occupies(mut self, class: ItemClass, set: NsSet) -> Self {
        self.occupies[class.index()] = set;
        self
    }

    /// Merges namespace `from` into the table of `into`: afterwards both (and
    /// everything already merged with either) share one table, so a name
    /// defined in one conflicts with and is found by the other.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Namespace, Policy};
    ///
    /// let p = Policy::new().with_merge(Namespace::Value, Namespace::Type);
    /// // Modules already share the type table, so all three are one table now.
    /// assert_eq!(p.table(Namespace::Value), p.table(Namespace::Module));
    /// ```
    #[must_use]
    pub const fn with_merge(mut self, from: Namespace, into: Namespace) -> Self {
        let old = self.merge[from.index()];
        let new = self.merge[into.index()];
        let mut i = 0;
        while i < 5 {
            if self.merge[i] as u8 == old as u8 {
                self.merge[i] = new;
            }
            i += 1;
        }
        self
    }

    /// Sets the shadowing rule for binders.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, Shadowing};
    ///
    /// assert_eq!(Policy::new().with_shadowing(Shadowing::DenyLocals).shadowing(), Shadowing::DenyLocals);
    /// ```
    #[must_use]
    pub const fn with_shadowing(mut self, shadowing: Shadowing) -> Self {
        self.shadowing = shadowing;
        self
    }

    /// Sets what duplicate definitions mean.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, Redefinition};
    ///
    /// let p = Policy::new().with_redefinition(Redefinition::LastWins);
    /// assert_eq!(p.redefinition(), Redefinition::LastWins);
    /// ```
    #[must_use]
    pub const fn with_redefinition(mut self, redefinition: Redefinition) -> Self {
        self.redefinition = redefinition;
        self
    }

    /// Sets what code inside a class sees of its members.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{ClassScope, Policy};
    ///
    /// let p = Policy::new().with_class_scope(ClassScope::Qualified);
    /// assert_eq!(p.class_scope(), ClassScope::Qualified);
    /// ```
    #[must_use]
    pub const fn with_class_scope(mut self, class_scope: ClassScope) -> Self {
        self.class_scope = class_scope;
        self
    }

    /// Sets whether nested modules see outer names.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{ModuleScope, Policy};
    ///
    /// let p = Policy::new().with_module_scope(ModuleScope::Lexical);
    /// assert_eq!(p.module_scope(), ModuleScope::Lexical);
    /// ```
    #[must_use]
    pub const fn with_module_scope(mut self, module_scope: ModuleScope) -> Self {
        self.module_scope = module_scope;
        self
    }

    /// Sets how `self::`, `parent::`, and `static::` bind.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, RootBinding};
    ///
    /// let p = Policy::new().with_roots(RootBinding::Early, RootBinding::Early, RootBinding::Late);
    /// assert_eq!(p.parent_root(), RootBinding::Early);
    /// ```
    #[must_use]
    pub const fn with_roots(
        mut self,
        self_root: RootBinding,
        parent_root: RootBinding,
        static_root: RootBinding,
    ) -> Self {
        self.roots = [self_root, parent_root, static_root];
        self
    }

    /// Sets whether visibility is enforced, and whether private items of a
    /// module are visible to its descendant modules.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Policy;
    ///
    /// let p = Policy::new().with_visibility(true, false);
    /// assert!(p.visibility_enforced());
    /// assert!(!p.private_to_descendants());
    /// ```
    #[must_use]
    pub const fn with_visibility(mut self, enforce: bool, private_to_descendants: bool) -> Self {
        self.enforce_visibility = enforce;
        self.private_to_descendants = private_to_descendants;
        self
    }

    /// Sets which import forms the language has, and how imports re-export.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, Reexport};
    ///
    /// let p = Policy::new().with_imports(false, true, Reexport::Never);
    /// assert!(!p.globs_allowed());
    /// assert!(p.aliases_allowed());
    /// ```
    #[must_use]
    pub const fn with_imports(mut self, globs: bool, aliases: bool, reexport: Reexport) -> Self {
        self.globs = globs;
        self.aliases = aliases;
        self.reexport = reexport;
        self
    }

    /// Sets whether a `global` declaration naming no known global binds a host
    /// global (`Res::Extern`) instead of being reported.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Policy;
    ///
    /// assert!(Policy::new().with_implicit_globals(true).implicit_globals());
    /// ```
    #[must_use]
    pub const fn with_implicit_globals(mut self, implicit: bool) -> Self {
        self.implicit_globals = implicit;
        self
    }

    // ------------------------------------------------------------ getters

    /// When items of `class` become visible.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Hoist, ItemClass, Policy};
    ///
    /// assert_eq!(Policy::new().hoisting(ItemClass::Fn), Hoist::Scope);
    /// ```
    #[must_use]
    pub const fn hoisting(&self, class: ItemClass) -> Hoist {
        self.hoist[class.index()]
    }

    /// The namespaces items of `class` define their name in (before merging).
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{ItemClass, Namespace, Policy};
    ///
    /// assert!(Policy::new().occupies(ItemClass::Fn).contains(Namespace::Value));
    /// ```
    #[must_use]
    pub const fn occupies(&self, class: ItemClass) -> NsSet {
        self.occupies[class.index()]
    }

    /// The table namespace `ns` is stored in after merging.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Namespace, Policy};
    ///
    /// assert_eq!(Policy::new().table(Namespace::Module), Namespace::Type);
    /// assert_eq!(Policy::new().table(Namespace::Value), Namespace::Value);
    /// ```
    #[must_use]
    pub const fn table(&self, ns: Namespace) -> Namespace {
        self.merge[ns.index()]
    }

    /// The shadowing rule.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, Shadowing};
    ///
    /// assert_eq!(Policy::new().shadowing(), Shadowing::Allow);
    /// ```
    #[must_use]
    pub const fn shadowing(&self) -> Shadowing {
        self.shadowing
    }

    /// What duplicate definitions mean.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, Redefinition};
    ///
    /// assert_eq!(Policy::php().redefinition(), Redefinition::Error);
    /// ```
    #[must_use]
    pub const fn redefinition(&self) -> Redefinition {
        self.redefinition
    }

    /// What code inside a class sees of its members.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{ClassScope, Policy};
    ///
    /// assert_eq!(Policy::new().class_scope(), ClassScope::Lexical);
    /// ```
    #[must_use]
    pub const fn class_scope(&self) -> ClassScope {
        self.class_scope
    }

    /// Whether nested modules see outer names.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{ModuleScope, Policy};
    ///
    /// assert_eq!(Policy::php().module_scope(), ModuleScope::Lexical);
    /// ```
    #[must_use]
    pub const fn module_scope(&self) -> ModuleScope {
        self.module_scope
    }

    /// How `self::` binds.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, RootBinding};
    ///
    /// assert_eq!(Policy::python().self_root(), RootBinding::Unsupported);
    /// ```
    #[must_use]
    pub const fn self_root(&self) -> RootBinding {
        self.roots[0]
    }

    /// How `parent::` binds.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, RootBinding};
    ///
    /// assert_eq!(Policy::kraken().parent_root(), RootBinding::Unsupported);
    /// ```
    #[must_use]
    pub const fn parent_root(&self) -> RootBinding {
        self.roots[1]
    }

    /// How `static::` binds.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, RootBinding};
    ///
    /// assert_eq!(Policy::php().static_root(), RootBinding::Late);
    /// ```
    #[must_use]
    pub const fn static_root(&self) -> RootBinding {
        self.roots[2]
    }

    /// Whether visibility (`Vis`) is enforced.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Policy;
    ///
    /// assert!(Policy::php().visibility_enforced());
    /// ```
    #[must_use]
    pub const fn visibility_enforced(&self) -> bool {
        self.enforce_visibility
    }

    /// Whether private items of a module are visible in its descendant
    /// modules (Rust's rule).
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Policy;
    ///
    /// assert!(Policy::new().private_to_descendants());
    /// ```
    #[must_use]
    pub const fn private_to_descendants(&self) -> bool {
        self.private_to_descendants
    }

    /// Whether glob imports are allowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Policy;
    ///
    /// assert!(Policy::python().globs_allowed());
    /// ```
    #[must_use]
    pub const fn globs_allowed(&self) -> bool {
        self.globs
    }

    /// Whether aliased imports (`use x as y`) are allowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Policy;
    ///
    /// assert!(Policy::php().aliases_allowed());
    /// ```
    #[must_use]
    pub const fn aliases_allowed(&self) -> bool {
        self.aliases
    }

    /// How imports re-export.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, Reexport};
    ///
    /// assert_eq!(Policy::php().reexport(), Reexport::Never);
    /// ```
    #[must_use]
    pub const fn reexport(&self) -> Reexport {
        self.reexport
    }

    /// Whether an unknown `global` name binds a host global.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Policy;
    ///
    /// assert!(!Policy::kraken().implicit_globals());
    /// ```
    #[must_use]
    pub const fn implicit_globals(&self) -> bool {
        self.implicit_globals
    }

    /// The export visibility of an import whose item says `declared`.
    pub(crate) const fn import_vis(&self, declared: Vis) -> Vis {
        match self.reexport {
            Reexport::AsDeclared => declared,
            Reexport::Always => Vis::Public,
            Reexport::Never => Vis::Private,
        }
    }

    /// The table index (`0..5`) of namespace `ns`.
    #[inline]
    pub(crate) const fn table_ix(&self, ns: Namespace) -> u8 {
        self.merge[ns.index()] as u8
    }
}

/// The rank of a visibility, for "the smaller of two" (glob re-exports).
pub(crate) const fn vis_rank(v: Vis) -> u8 {
    match v {
        Vis::Private => 0,
        Vis::Protected => 1,
        Vis::Package => 2,
        Vis::Public => 3,
    }
}

/// The narrower of two visibilities.
pub(crate) const fn min_vis(a: Vis, b: Vis) -> Vis {
    if vis_rank(a) <= vis_rank(b) { a } else { b }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_merge_is_transitive() {
        let p = Policy::new()
            .with_merge(Namespace::Macro, Namespace::Value)
            .with_merge(Namespace::Value, Namespace::Type);
        assert_eq!(p.table(Namespace::Macro), Namespace::Type);
        assert_eq!(p.table(Namespace::Value), Namespace::Type);
        assert_eq!(p.table(Namespace::Module), Namespace::Type);
        assert_eq!(p.table(Namespace::Label), Namespace::Label);
    }

    #[test]
    fn test_min_vis_orders_private_lowest() {
        assert_eq!(min_vis(Vis::Public, Vis::Private), Vis::Private);
        assert_eq!(min_vis(Vis::Package, Vis::Public), Vis::Package);
        assert_eq!(min_vis(Vis::Protected, Vis::Package), Vis::Protected);
    }

    #[test]
    fn test_import_vis_follows_reexport() {
        assert_eq!(Policy::new().import_vis(Vis::Public), Vis::Public);
        assert_eq!(Policy::new().import_vis(Vis::Private), Vis::Private);
        assert_eq!(Policy::python().import_vis(Vis::Private), Vis::Public);
        assert_eq!(Policy::php().import_vis(Vis::Public), Vis::Private);
    }

    #[test]
    fn test_namespace_index_round_trips() {
        for ns in Namespace::ALL {
            assert_eq!(Namespace::from_index(ns.index()), ns);
        }
    }
}
