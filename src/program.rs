//! The drivers: [`Program`] (several units resolved against each other),
//! [`Resolver`] (one unit), and their result, [`Resolution`].

use alloc::vec::Vec;

use hir_lang::{
    DefId, Hir, HirError, ItemId, ItemKind, Name, NodeRef, Pat, PatId, PathId, Res, UnitId, Vis,
};
use intern_lang::Lookup;

use crate::{
    collect::{Bases, collect},
    diag::{DiagKind, Diagnostic},
    env::{Env, NoEnv},
    error::{Budget, ResolveError},
    imports::resolve_imports,
    index::{Index, RawRef, Target, UnitInput},
    members::{Members, finish_deferred},
    model::{Model, ScopeKind, Unit, ix},
    pass::{Pass, UnitOut, entry_gate},
    policy::{Namespace, Policy},
    suggest::Suggester,
};

/// One member of a class's effective member table: its own members and
/// those its mixins contribute, after `insteadof` and `as` rules.
///
/// # Examples
///
/// ```
/// use hir_lang::{Name, Res, Symbol, Vis};
/// use resolve_lang::{ClassMember, Namespace};
///
/// let m = ClassMember {
///     name: Name::new(Symbol::from_u32(1).unwrap()),
///     namespace: Namespace::Value,
///     res: Res::Err,
///     vis: Vis::Public,
///     mixin: None,
/// };
/// assert!(m.mixin.is_none());
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClassMember {
    /// The member's name in this class (an alias's new name).
    pub name: Name,
    /// The table it lives in (after merging).
    pub namespace: Namespace,
    /// What it resolves to (for a mixin member, the mixin's item).
    pub res: Res,
    /// Its visibility in this class (a rule may change it).
    pub vis: Vis,
    /// The mixin it came from, or `None` for the class's own member.
    pub mixin: Option<DefId>,
}

/// One resolved unit.
///
/// # Examples
///
/// ```
/// use hir_lang::Builder;
/// use intern_lang::Interner;
///
/// let mut b = Builder::new();
/// let root = b.module(None, &[]);
/// let res = resolve_lang::resolve(b.finish(root)?, &Interner::new())?;
/// assert_eq!(res.units().len(), 1);
/// assert!(res.units()[0].hir().validate().is_ok());
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Debug)]
pub struct ResolvedUnit {
    name: Option<Name>,
    hir: Hir,
    members: Vec<(ItemId, Vec<ClassMember>)>,
    ident_matches: Vec<PatId>,
}

impl ResolvedUnit {
    /// The unit's id.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, UnitId};
    /// use intern_lang::Interner;
    ///
    /// let mut b = Builder::for_unit(UnitId::new(4));
    /// let root = b.module(None, &[]);
    /// let res = resolve_lang::resolve(b.finish(root)?, &Interner::new())?;
    /// assert_eq!(res.units()[0].id(), UnitId::new(4));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn id(&self) -> UnitId {
        self.hir.unit()
    }

    /// The root name other units reached this unit by, if it had one.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use intern_lang::Interner;
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let res = resolve_lang::resolve(b.finish(root)?, &Interner::new())?;
    /// assert!(res.units()[0].name().is_none());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        self.name
    }

    /// The resolved HIR: every resolvable path's slot is filled through
    /// hir-lang's checked setters, so it is still a valid `Hir`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use intern_lang::Interner;
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let res = resolve_lang::resolve(b.finish(root)?, &Interner::new())?;
    /// assert_eq!(res.units()[0].hir().root(), root);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn hir(&self) -> &Hir {
        &self.hir
    }

    /// Takes the resolved HIR.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use intern_lang::Interner;
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let res = resolve_lang::resolve(b.finish(root)?, &Interner::new())?;
    /// let (units, _, _) = res.into_parts();
    /// let hir = units.into_iter().next().unwrap().into_hir();
    /// assert!(hir.validate().is_ok());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn into_hir(self) -> Hir {
        self.hir
    }

    /// The effective members of a class or interface item (its own members
    /// plus what its mixins contribute), sorted by namespace, then by name
    /// (symbol order, not spelling).
    /// `None` for other items.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, ClassDef, Item, ItemKind, Name};
    /// use intern_lang::Interner;
    ///
    /// let mut names = Interner::new();
    /// let mut b = Builder::new();
    /// let body = b.block(&[], None);
    /// let m = b.func(Name::new(names.intern("m")), &[], body);
    /// let items = b.list(&[m]);
    /// let class = b.item(Item::new(Some(Name::new(names.intern("C"))), ItemKind::Class(ClassDef { items, ..ClassDef::default() })));
    /// let root = b.module(None, &[class]);
    /// let res = resolve_lang::resolve(b.finish(root)?, &names)?;
    /// assert_eq!(res.units()[0].members(class).map(<[_]>::len), Some(1));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn members(&self, class: ItemId) -> Option<&[ClassMember]> {
        let i = self
            .members
            .binary_search_by_key(&class, |(c, _)| *c)
            .ok()?;
        self.members.get(i).map(|(_, m)| m.as_slice())
    }

    /// For a `Pat::Ident` pattern: `Some(true)` if it binds its binder,
    /// `Some(false)` if its path named a constant, unit variant, or unit
    /// record (it matches that value). `None` for other patterns.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, PatId};
    /// use intern_lang::Interner;
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let res = resolve_lang::resolve(b.finish(root)?, &Interner::new())?;
    /// assert_eq!(res.units()[0].ident_binds(PatId::from_index(0).unwrap()), None);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn ident_binds(&self, pat: PatId) -> Option<bool> {
        matches!(self.hir.get_pat(pat), Some(Pat::Ident { .. }))
            .then(|| self.ident_matches.binary_search(&pat).is_err())
    }
}

/// The result of resolving a program: the resolved units, every diagnostic,
/// and the definition/reference index.
///
/// # Examples
///
/// ```
/// use hir_lang::{Builder, Name};
/// use intern_lang::Interner;
///
/// let mut names = Interner::new();
/// let mut b = Builder::new();
/// let missing = b.name_expr(Name::new(names.intern("missing")));
/// let body = b.block(&[], Some(missing));
/// let f = b.func(Name::new(names.intern("f")), &[], body);
/// let root = b.module(None, &[f]);
/// let res = resolve_lang::resolve(b.finish(root)?, &names)?;
/// assert!(!res.is_clean());
/// assert_eq!(res.diagnostics()[0].message(&names), "cannot find value `missing` in this scope");
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Debug)]
pub struct Resolution {
    units: Vec<ResolvedUnit>,
    diagnostics: Vec<Diagnostic>,
    index: Index,
}

impl Resolution {
    /// The resolved units, in the order they were added.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use intern_lang::Interner;
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let res = resolve_lang::resolve(b.finish(root)?, &Interner::new())?;
    /// assert_eq!(res.units().len(), 1);
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn units(&self) -> &[ResolvedUnit] {
        &self.units
    }

    /// One unit by id.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, UnitId};
    /// use intern_lang::Interner;
    ///
    /// let mut b = Builder::for_unit(UnitId::new(2));
    /// let root = b.module(None, &[]);
    /// let res = resolve_lang::resolve(b.finish(root)?, &Interner::new())?;
    /// assert!(res.unit(UnitId::new(2)).is_some());
    /// assert!(res.unit(UnitId::new(3)).is_none());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn unit(&self, id: UnitId) -> Option<&ResolvedUnit> {
        self.units.iter().find(|u| u.id() == id)
    }

    /// The resolved HIR of one unit.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, UnitId};
    /// use intern_lang::Interner;
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let res = resolve_lang::resolve(b.finish(root)?, &Interner::new())?;
    /// assert!(res.hir(UnitId::new(0)).is_some());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn hir(&self, id: UnitId) -> Option<&Hir> {
        self.unit(id).map(ResolvedUnit::hir)
    }

    /// Every diagnostic, sorted by unit, then position, then discovery.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use intern_lang::Interner;
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let res = resolve_lang::resolve(b.finish(root)?, &Interner::new())?;
    /// assert!(res.diagnostics().is_empty());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// Whether resolution found nothing to report.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use intern_lang::Interner;
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// assert!(resolve_lang::resolve(b.finish(root)?, &Interner::new())?.is_clean());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.diagnostics.is_empty()
    }

    /// The definition/reference index.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use intern_lang::Interner;
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let res = resolve_lang::resolve(b.finish(root)?, &Interner::new())?;
    /// assert!(res.index().references_all().is_empty());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn index(&self) -> &Index {
        &self.index
    }

    /// Takes the parts.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use intern_lang::Interner;
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let (units, diags, _index) = resolve_lang::resolve(b.finish(root)?, &Interner::new())?.into_parts();
    /// assert_eq!((units.len(), diags.len()), (1, 0));
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    #[must_use]
    pub fn into_parts(self) -> (Vec<ResolvedUnit>, Vec<Diagnostic>, Index) {
        (self.units, self.diagnostics, self.index)
    }
}

/// Resolves one unit (Tier 2): a policy, an environment, a budget.
///
/// # Examples
///
/// ```
/// use hir_lang::{Builder, Name, Prim, Res};
/// use intern_lang::Interner;
/// use resolve_lang::{DefKind, Export, MapEnv, Namespace, Policy, Resolver};
///
/// let mut names = Interner::new();
/// let int = Name::new(names.intern("int"));
/// let env = MapEnv::new().with_prelude(int, Namespace::Type, Export::new(Res::Prim(Prim::I64), DefKind::Prim));
///
/// // const N: int = 1
/// let mut b = Builder::new();
/// let ty_path = b.name_path(int, hir_lang::Ns::Type);
/// let ty = b.ty(hir_lang::Ty::Path(ty_path));
/// let one = b.int(1);
/// let n = b.item(hir_lang::Item::new(Some(Name::new(names.intern("N"))), hir_lang::ItemKind::Const { ty: Some(ty), value: Some(one) }));
/// let root = b.module(None, &[n]);
///
/// let res = Resolver::new(Policy::kraken()).with_env(&env).resolve(b.finish(root)?, &names)?;
/// assert!(res.is_clean());
/// assert_eq!(res.units()[0].hir().path(ty_path).res, Res::Prim(Prim::I64));
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy)]
pub struct Resolver<'e> {
    policy: Policy,
    env: &'e dyn Env,
    budget: Budget,
}

impl core::fmt::Debug for Resolver<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Resolver")
            .field("policy", &self.policy)
            .field("budget", &self.budget)
            .finish_non_exhaustive()
    }
}

impl Resolver<'static> {
    /// A resolver with `policy`, no environment, and the default budget.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, Resolver};
    ///
    /// let _r = Resolver::new(Policy::python());
    /// ```
    #[must_use]
    pub fn new(policy: Policy) -> Self {
        Self {
            policy,
            env: &NoEnv,
            budget: Budget::default(),
        }
    }
}

impl Resolver<'_> {
    /// Uses `env` for names outside the unit.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{MapEnv, Policy, Resolver};
    ///
    /// let env = MapEnv::new();
    /// let _r = Resolver::new(Policy::new()).with_env(&env);
    /// ```
    #[must_use]
    pub fn with_env(self, env: &dyn Env) -> Resolver<'_> {
        Resolver {
            policy: self.policy,
            env,
            budget: self.budget,
        }
    }

    /// Sets the budget.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Budget, Policy, Resolver};
    ///
    /// let _r = Resolver::new(Policy::new()).with_budget(Budget::unlimited());
    /// ```
    #[must_use]
    pub fn with_budget(mut self, budget: Budget) -> Self {
        self.budget = budget;
        self
    }

    /// Resolves `hir`.
    ///
    /// # Errors
    ///
    /// [`ResolveError::BudgetExceeded`] if the unit exceeds the budget.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use intern_lang::Interner;
    /// use resolve_lang::{Policy, Resolver};
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let res = Resolver::new(Policy::php()).resolve(b.finish(root)?, &Interner::new())?;
    /// assert!(res.is_clean());
    /// # Ok::<(), Box<dyn std::error::Error>>(())
    /// ```
    pub fn resolve<L: Lookup>(self, hir: Hir, names: &L) -> Result<Resolution, ResolveError> {
        let mut program = Program::new(self.policy)
            .with_env(self.env)
            .with_budget(self.budget);
        program.add_unit(None, hir);
        program.resolve(names)
    }
}

/// Several units resolved against each other (Tier 3): the in-memory
/// multi-unit driver. Each unit may be given a root name, by which every
/// unit (itself included) can reach its root module as a path's first
/// segment (`util::helper`, `import util`). Imports may form cycles across
/// units.
///
/// # Examples
///
/// ```
/// use hir_lang::{Builder, Def, Expr, FnDef, Item, ItemKind, Name, Ns, Path, Res, Segment, UnitId, Vis};
/// use intern_lang::Interner;
/// use resolve_lang::{Policy, Program};
///
/// let mut names = Interner::new();
/// let (util, helper) = (Name::new(names.intern("util")), Name::new(names.intern("helper")));
///
/// // Unit 1, reachable as `util`: pub fn helper() {}
/// let mut b = Builder::for_unit(UnitId::new(1));
/// let body = b.block(&[], None);
/// let f = b.item(Item::new(Some(helper), ItemKind::Fn(FnDef { body: Some(body), ..FnDef::default() })).with_vis(Vis::Public));
/// let root = b.module(None, &[f]);
/// let util_hir = b.finish(root)?;
///
/// // Unit 2: fn main() { util::helper }
/// let mut b = Builder::for_unit(UnitId::new(2));
/// let segs = [Segment::new(util, b.origin()), Segment::new(helper, b.origin())];
/// let segs = b.list(&segs);
/// let path = b.path(Path::new(segs, Ns::Value));
/// let call = b.expr(Expr::Path(path));
/// let body = b.block(&[], Some(call));
/// let main = b.func(Name::new(names.intern("main")), &[], body);
/// let root = b.module(None, &[main]);
/// let app_hir = b.finish(root)?;
///
/// let mut program = Program::new(Policy::kraken());
/// program.add_unit(Some(util), util_hir);
/// program.add_unit(None, app_hir);
/// let res = program.resolve(&names)?;
/// assert!(res.is_clean());
/// let app = res.hir(UnitId::new(2)).unwrap();
/// let Res::Def(d) = app.path(path).res else { panic!("unresolved") };
/// assert_eq!((d.unit(), d.def()), (UnitId::new(1), Def::Item(f)));
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub struct Program<'e> {
    policy: Policy,
    env: &'e dyn Env,
    budget: Budget,
    units: Vec<(Option<Name>, u32, Hir)>,
}

impl core::fmt::Debug for Program<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Program")
            .field("policy", &self.policy)
            .field("budget", &self.budget)
            .field("units", &self.units.len())
            .finish_non_exhaustive()
    }
}

impl Program<'static> {
    /// An empty program with `policy`, no environment, and the default
    /// budget.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, Program};
    ///
    /// let p = Program::new(Policy::kraken());
    /// assert_eq!(p.len(), 0);
    /// ```
    #[must_use]
    pub fn new(policy: Policy) -> Self {
        Self {
            policy,
            env: &NoEnv,
            budget: Budget::default(),
            units: Vec::new(),
        }
    }
}

impl Program<'_> {
    /// Uses `env` for names outside the program.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{MapEnv, Policy, Program};
    ///
    /// let env = MapEnv::new();
    /// let _p = Program::new(Policy::new()).with_env(&env);
    /// ```
    #[must_use]
    pub fn with_env(self, env: &dyn Env) -> Program<'_> {
        Program {
            policy: self.policy,
            env,
            budget: self.budget,
            units: self.units,
        }
    }

    /// Sets the budget.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Budget, Policy, Program};
    ///
    /// let _p = Program::new(Policy::new()).with_budget(Budget::default().with_glob_bindings(10));
    /// ```
    #[must_use]
    pub fn with_budget(mut self, budget: Budget) -> Self {
        self.budget = budget;
        self
    }

    /// Adds a unit in package 0, reachable by `name` (if given) from every
    /// unit.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use resolve_lang::{Policy, Program};
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let mut p = Program::new(Policy::new());
    /// p.add_unit(None, b.finish(root)?);
    /// assert_eq!(p.len(), 1);
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    pub fn add_unit(&mut self, name: Option<Name>, hir: Hir) {
        self.units.push((name, 0, hir));
    }

    /// Adds a unit to a package: `Vis::Package` items are visible across
    /// units of the same package only.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use resolve_lang::{Policy, Program};
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let mut p = Program::new(Policy::new());
    /// p.add_unit_in(7, None, b.finish(root)?);
    /// assert!(!p.is_empty());
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    pub fn add_unit_in(&mut self, package: u32, name: Option<Name>, hir: Hir) {
        self.units.push((name, package, hir));
    }

    /// The number of units added.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, Program};
    ///
    /// assert_eq!(Program::new(Policy::new()).len(), 0);
    /// ```
    #[must_use]
    pub fn len(&self) -> usize {
        self.units.len()
    }

    /// Whether no unit was added.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{Policy, Program};
    ///
    /// assert!(Program::new(Policy::new()).is_empty());
    /// ```
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.units.is_empty()
    }

    /// Resolves every unit.
    ///
    /// # Errors
    ///
    /// - [`ResolveError::DuplicateUnit`] if two units share a `UnitId`.
    /// - [`ResolveError::BudgetExceeded`] if the program exceeds the budget.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, UnitId};
    /// use intern_lang::Interner;
    /// use resolve_lang::{Policy, Program, ResolveError};
    ///
    /// let mut p = Program::new(Policy::new());
    /// for _ in 0..2 {
    ///     let mut b = Builder::for_unit(UnitId::new(1));
    ///     let root = b.module(None, &[]);
    ///     p.add_unit(None, b.finish(root)?);
    /// }
    /// assert_eq!(p.resolve(&Interner::new()).unwrap_err(), ResolveError::DuplicateUnit { unit: UnitId::new(1) });
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    pub fn resolve<L: Lookup>(self, names: &L) -> Result<Resolution, ResolveError> {
        let mut unit_ix: Vec<(UnitId, u32)> = self
            .units
            .iter()
            .enumerate()
            .map(|(i, (_, _, h))| (h.unit(), ix(i)))
            .collect();
        unit_ix.sort();
        if let Some(w) = unit_ix
            .windows(2)
            .find(|w| w.first().map(|x| x.0) == w.get(1).map(|x| x.0))
        {
            if let Some(&(unit, _)) = w.first() {
                return Err(ResolveError::DuplicateUnit { unit });
            }
        }
        let mut m = Model {
            policy: self.policy,
            env: self.env,
            units: Vec::with_capacity(self.units.len()),
            unit_ix,
            roots: Vec::new(),
            scopes: Vec::new(),
            bindings: Vec::new(),
            imports: Vec::new(),
            sums: Vec::new(),
            diags: Vec::new(),
        };
        // Phase 1: collect.
        for (u, (name, package, hir)) in self.units.into_iter().enumerate() {
            let bases = Bases {
                unit: ix(u),
                scope: ix(m.scopes.len()),
                binding: ix(m.bindings.len()),
                import: ix(m.imports.len()),
                sum: ix(m.sums.len()),
            };
            let c = collect(&hir, &m.policy, bases);
            m.scopes.extend(c.scopes);
            m.bindings.extend(c.bindings);
            m.imports.extend(c.imports);
            m.sums.extend(c.sums);
            if let Some(name) = name {
                m.roots.push((name, ix(u)));
            }
            m.units.push(Unit {
                id: hir.unit(),
                name,
                package,
                hir,
                root_scope: c.root_scope,
                item_scope: c.item_scope,
                block_scope: c.block_scope,
                sum_table: c.sum_table,
                import_of: c.import_of,
                after_decl: Vec::new(),
            });
            for (kind, span, node) in c.diags {
                m.report(ix(u), kind, span, Some(node));
            }
        }
        // The first unit to claim a root name keeps it.
        m.roots.sort_by_key(|(n, u)| (*n, *u));
        m.roots.dedup_by_key(|(n, _)| *n);
        let mut sugg = Suggester::new(self.budget.suggestion_cells());
        // Phase 2: imports.
        resolve_imports(&mut m, names, &mut sugg, self.budget.glob_bindings())?;
        // Declare-before-use entries, by gating item.
        let mut gated: Vec<Vec<(u32, u32, u32)>> = m.units.iter().map(|_| Vec::new()).collect();
        for (s, scope) in m.scopes.iter().enumerate() {
            for (e, entry) in scope.table.iter().enumerate() {
                if let Some(item) = entry_gate(&m, entry.state) {
                    if let Some(list) = gated.get_mut(scope.unit as usize) {
                        list.push((ix(item.index()), ix(s), ix(e)));
                    }
                }
            }
        }
        for (unit, mut list) in m.units.iter_mut().zip(gated) {
            list.sort_unstable();
            unit.after_decl = list;
        }
        // Phase 3: the walk.
        let mut outs: Vec<UnitOut> = Vec::with_capacity(m.units.len());
        for u in 0..m.units.len() {
            if let Some(pass) = Pass::new(&m, names, &mut sugg, ix(u)) {
                outs.push(pass.run());
            }
        }
        // Phase 4: members, mixins, deferred paths.
        let mut members = Members::build(&mut m, &outs, self.budget.member_steps());
        finish_deferred(&m, &mut members, &mut outs)?;
        // Apply plans to the HIR.
        for (unit, out) in m.units.iter_mut().zip(outs.iter_mut()) {
            apply(unit, out);
        }
        Ok(assemble(m, outs, &members))
    }
}

/// Writes the planned resolutions through hir-lang's checked setters.
fn apply(unit: &mut Unit, out: &mut UnitOut) {
    let id = unit.id;
    for i in 0..out.plan.len() {
        let Some((res, unresolved)) = out.plan.get(i).copied().flatten() else {
            continue;
        };
        let Some(p) = PathId::from_index(i) else {
            continue;
        };
        let Err(error) = unit.hir.resolve_partial(p, res, unresolved) else {
            continue;
        };
        // Keep the HIR valid: an error resolution is accepted everywhere.
        let _always_ok = unit.hir.resolve(p, Res::Err);
        if let Some(slot) = out.plan.get_mut(i) {
            *slot = Some((Res::Err, 0));
        }
        let span = unit
            .hir
            .list(unit.hir.path(p).segments)
            .first()
            .map_or(unit.hir.origin(NodeRef::Path(p)).span, |s| s.origin.span);
        let kind = match error {
            HirError::OutOfScope { binder, .. } | HirError::NotCapturable { binder, .. } => {
                let name = unit.hir.binder(binder).map(|b| b.name);
                match name {
                    Some(name) => DiagKind::CannotCapture { name, binder },
                    None => DiagKind::Rejected { error },
                }
            }
            _ => DiagKind::Rejected { error },
        };
        out.diag(id, p, kind, span, false);
    }
}

/// Builds the result: units, sorted diagnostics, index.
fn assemble(m: Model<'_>, outs: Vec<UnitOut>, members: &Members) -> Resolution {
    let mut diagnostics = m.diags.clone();
    for out in &outs {
        diagnostics.extend(out.diags.iter().copied());
    }
    let order: Vec<UnitId> = m.units.iter().map(|u| u.id).collect();
    let pos = |id: UnitId| order.iter().position(|u| *u == id).unwrap_or(usize::MAX);
    diagnostics.sort_by_key(|d| (pos(d.unit), d.span.start(), d.span.end()));
    // Index input per unit.
    let mut inputs_refs: Vec<(Vec<RawRef>, Vec<hir_lang::BinderId>, Vec<ItemId>)> = Vec::new();
    for (u, out) in outs.iter().enumerate() {
        let Some(unit) = m.units.get(u) else { continue };
        let mut refs = Vec::with_capacity(out.segs.len());
        for s in &out.segs {
            if unit.hir.path(s.path).res == Res::Err {
                continue;
            }
            let Some(target) = target_of(unit, s.res) else {
                continue;
            };
            let via = m
                .imports
                .get(s.via as usize)
                .filter(|imp| is_alias(&m, imp.unit, imp.item))
                .and_then(|imp| {
                    m.units
                        .get(imp.unit as usize)
                        .map(|x| Target::Import(x.id, imp.item))
                });
            refs.push(RawRef {
                path: s.path,
                seg: s.seg,
                target,
                via,
            });
        }
        let dead: Vec<hir_lang::BinderId> = out
            .ident_matches
            .iter()
            .filter_map(|p| match unit.hir.get_pat(*p) {
                Some(Pat::Ident { binder, .. }) => Some(*binder),
                _ => None,
            })
            .collect();
        let aliases: Vec<ItemId> = m
            .imports
            .iter()
            .filter(|imp| imp.unit == ix(u) && is_alias(&m, imp.unit, imp.item))
            .map(|imp| imp.item)
            .collect();
        inputs_refs.push((refs, dead, aliases));
    }
    let inputs: Vec<UnitInput<'_>> = m
        .units
        .iter()
        .zip(inputs_refs)
        .map(|(unit, (refs, dead_binders, mut aliases))| {
            aliases.sort();
            UnitInput {
                hir: &unit.hir,
                refs,
                dead_binders,
                aliases,
            }
        })
        .collect();
    let index = Index::build(&inputs);
    drop(inputs);
    // Class members per unit.
    let mut class_members: Vec<Vec<(ItemId, Vec<ClassMember>)>> =
        m.units.iter().map(|_| Vec::new()).collect();
    for (s, scope) in m.scopes.iter().enumerate() {
        let ScopeKind::Type(item, _) = scope.kind else {
            continue;
        };
        let list: Vec<ClassMember> = members
            .tables
            .get(s)
            .into_iter()
            .flatten()
            .filter_map(|mem| {
                let b = m.bindings.get(mem.binding as usize)?;
                let mixin = match mem.from {
                    Some(Res::Def(d)) => Some(d),
                    _ => None,
                };
                Some(ClassMember {
                    name: mem.name,
                    namespace: Namespace::from_index(mem.ns as usize),
                    res: b.res,
                    vis: b.vis,
                    mixin,
                })
            })
            .collect();
        if let Some(v) = class_members.get_mut(scope.unit as usize) {
            v.push((item, list));
        }
    }
    let mut units = Vec::with_capacity(m.units.len());
    for ((unit, out), mut cm) in m.units.into_iter().zip(outs).zip(class_members) {
        cm.sort_by_key(|(i, _)| *i);
        let mut ident_matches = out.ident_matches;
        ident_matches.sort();
        ident_matches.dedup();
        units.push(ResolvedUnit {
            name: unit.name,
            hir: unit.hir,
            members: cm,
            ident_matches,
        });
    }
    Resolution {
        units,
        diagnostics,
        index,
    }
}

/// Whether an import item renames what it imports.
fn is_alias(m: &Model<'_>, u: u32, item: ItemId) -> bool {
    let Some(unit) = m.units.get(u as usize) else {
        return false;
    };
    let it = unit.hir.item(item);
    let ItemKind::Import { path, glob: false } = it.kind else {
        return false;
    };
    let last = unit
        .hir
        .list(unit.hir.path(path).segments)
        .last()
        .map(|s| s.name);
    it.name.is_some() && it.name != last
}

/// The index target of a resolution in `unit`.
fn target_of(unit: &Unit, res: Res) -> Option<Target> {
    match res {
        Res::Def(d) => Some(Target::Def(d)),
        Res::Local(b) => Some(Target::Local(unit.id, b)),
        Res::Extern(s) => Some(Target::Extern(s)),
        Res::Prim(_) | Res::Err | Res::Unresolved => None,
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use hir_lang::{BinderKind, Expr, Stmt};

    use super::*;
    use crate::model::fixture::*;

    #[test]
    fn test_apply_turns_refused_resolutions_into_diagnostics() {
        // fn f() { let x = 1; fn g() { x } } — plan `x` to the local anyway.
        let mut f = Fixture::new();
        let (x, g, fname) = (f.name("x"), f.name("g"), f.name("f"));
        let bx = f.b.new_binder(x, BinderKind::Local);
        let pat = f.b.bind(bx);
        let one = f.b.int(1);
        let s = f.b.let_stmt(pat, Some(one));
        let use_x = f.b.name_expr(x);
        let gb = f.b.block(&[], Some(use_x));
        let gi = f.b.func(g, &[], gb);
        let si = f.b.stmt(Stmt::Item(gi));
        let body = f.b.block(&[s, si], None);
        let fi = f.b.func(fname, &[], body);
        let root = f.b.module(None, &[fi]);
        let hir = f.finish(root);
        // `name_expr` made the unit's only path.
        let p = PathId::from_index(0).unwrap();
        assert_eq!(*hir.expr(use_x), Expr::Path(p));
        let (mut m, mut outs) = walked(hir, &f.names, Policy::new());
        // The walk already refused it; force the plan to exercise `apply`.
        outs[0].plan[p.index()] = Some((Res::Local(bx), 0));
        outs[0].diagnosed[p.index()] = false;
        outs[0].diags.clear();
        apply(&mut m.units[0], &mut outs[0]);
        assert_eq!(m.units[0].hir.path(p).res, Res::Err);
        assert!(matches!(
            outs[0].diags[..],
            [Diagnostic {
                kind: DiagKind::CannotCapture { .. },
                ..
            }]
        ));
        assert!(m.units[0].hir.validate().is_ok());
    }

    #[test]
    fn test_ident_binds_only_for_ident_patterns() {
        let mut f = Fixture::new();
        let root = f.b.module(None, &[]);
        let hir = f.finish(root);
        let unit = ResolvedUnit {
            name: None,
            hir,
            members: Vec::new(),
            ident_matches: Vec::new(),
        };
        assert_eq!(unit.ident_binds(PatId::from_index(0).unwrap()), None);
        assert!(unit.members(ItemId::from_index(0).unwrap()).is_none());
    }
}
