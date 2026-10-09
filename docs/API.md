# resolve-lang &mdash; API Reference

> Complete reference for every public item in `resolve-lang`, with examples.
> **Status: 0.3.0, pre-1.0.** The surface is designed across the 0.x series and
> frozen at `1.0.0`, after the LexerSketch LSP drives go-to-definition and
> rename through it (see [`../dev/ROADMAP.md`](../dev/ROADMAP.md)).

<sub>Copyright &copy; 2026 <strong>James Gober</strong>.</sub>

## Table of contents

- [Overview](#overview)
- [Installation](#installation)
- [Quick start](#quick-start)
- [Concepts](#concepts)
  - [Phases](#phases)
  - [Lexical lookup](#lexical-lookup)
  - [Paths and partial resolution](#paths-and-partial-resolution)
  - [Imports as a fixpoint](#imports-as-a-fixpoint)
  - [Bare identifier patterns](#bare-identifier-patterns)
  - [Classes, members, and mixins](#classes-members-and-mixins)
  - [Case folding](#case-folding)
  - [What every path ends as](#what-every-path-ends-as)
- [`resolve`](#resolve)
- [`Policy`](#policy)
  - [`Policy::new`](#policynew), [`Policy::kraken`](#policykraken), [`Policy::php`](#policyphp), [`Policy::python`](#policypython)
  - [Setters](#policy-setters)
  - [Getters](#policy-getters)
- [`Namespace`](#namespace), [`NsSet`](#nsset), and [`Case`](#case)
- [`ItemClass`](#itemclass)
- [`Hoist`](#hoist), [`Shadowing`](#shadowing), [`Redefinition`](#redefinition), [`ClassScope`](#classscope), [`ModuleScope`](#modulescope), [`RootBinding`](#rootbinding), [`Reexport`](#reexport)
- [`Env`](#env), [`Export`](#export), [`DefKind`](#defkind), [`NoEnv`](#noenv), [`MapEnv`](#mapenv)
- [`Resolver`](#resolver)
- [`Program`](#program)
- [`Resolution`](#resolution)
- [`ResolvedUnit`](#resolvedunit) and [`ClassMember`](#classmember)
- [`Diagnostic`](#diagnostic) and [`DiagKind`](#diagkind)
- [`Budget`](#budget), [`ResolveError`](#resolveerror), [`Limit`](#limit)
- [`Index`](#index)
  - [`Definition`](#definition), [`Reference`](#reference), [`References`](#references), [`DefRef`](#defref), [`Target`](#target), [`Location`](#location), [`Occurrence`](#occurrence), [`RenameSet`](#renameset), [`SymbolKind`](#symbolkind)
- [Feature flags](#feature-flags)
- [Limits and complexity](#limits-and-complexity)
- [What is not done yet](#what-is-not-done-yet)

## Overview

`resolve-lang` binds the names of a [`hir_lang::Hir`](https://docs.rs/hir-lang)
to what they name. It reads binders through hir-lang's `lookup_local` and walk
events, item and import tables it builds itself, class member tables with mixins
expanded, and the host's [`Env`](#env), all under a language's [`Policy`](#policy).
It writes each resolution back through `Hir::resolve_partial`, reports what does
not resolve as [`Diagnostic`](#diagnostic)s, and builds an [`Index`](#index) of
definitions and references.

## Installation

```toml
[dependencies]
resolve-lang = "0.3"
hir-lang = "0.3"
intern-lang = "1"
```

## Quick start

```rust
use hir_lang::{Builder, Expr, Name, Res};
use intern_lang::Interner;

// fn id(x) { x }
let mut names = Interner::new();
let x = Name::new(names.intern("x"));
let mut b = Builder::new();
let (param, binder) = b.local_param(x);
let use_x = b.name_expr(x);
let body = b.block(&[], Some(use_x));
let f = b.func(Name::new(names.intern("id")), &[param], body);
let root = b.module(None, &[f]);
let hir = b.finish(root)?;
let unit = hir.unit();

let res = resolve_lang::resolve(hir, &names)?;
assert!(res.is_clean());
let hir = res.hir(unit).unwrap();
let Expr::Path(p) = *hir.expr(use_x) else { unreachable!() };
assert_eq!(hir.path(p).res, Res::Local(binder));
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Concepts

### Phases

1. **Collect.** One walk per unit records every scope that holds items (modules,
   classes, interfaces, blocks with item statements), the definitions in each by
   namespace, and the imports. The redefinition rule runs here.
2. **Imports.** Every import of every unit is resolved jointly (see
   [Imports as a fixpoint](#imports-as-a-fixpoint)); each scope gets its final
   table.
3. **Walk.** One walk per unit resolves every path. Paths that need class member
   tables are planned partially; an unqualified name inside a class whose
   inherited members it might name is resolved and set aside.
4. **Members.** Class member tables are built, mixins expanded in dependency
   order, every class with several bases linearized (C3), and the deferred
   paths finished.
5. **Apply and index.** Each planned resolution is written with
   `Hir::resolve_partial`; the index is built.

### Lexical lookup

A path's first segment is looked up innermost-out. Binders come from
`Hir::lookup_local` (hir-lang's scope rule: a `let` binder is visible after its
statement, a parameter in the body, and so on). Items, imports, and glob
imports come from per-name shadow stacks the walk pushes when their scope opens
(or, for declare-before-use items, when the declaration is reached) and pops
when it closes. A binder and an item compete by scope depth and position: the
innermost wins, and in one scope the one that became visible last. If the
winner is a local behind a frame it cannot cross (a nested function), the path
is reported as [`CannotCapture`](#diagkind) rather than falling back outward.

After the lexical scopes: the program's unit roots and the environment's roots
(for the first segment of a longer path or an import), then the prelude.

| Path namespace | Tables searched for the last segment | For a prefix segment |
|---|---|---|
| `Value`, the callee of a call | value, then constant | module, type |
| `Value`, anywhere else | constant, then value | module, type |
| `Type` | type | module, type |
| `Pattern` | constant, then value (then filtered: constants, unit variants, unit records) | module, type |
| `Import` | value, type, module, macro, constant (one binding per table found) | module, type |
| `Region` | binders only | &mdash; |

Tables are after [merging](#namespace): by default constants share the value
table (so the two orders are one lookup); with `Policy::python()`, all of them
are one table. Under `Policy::php()` the constant table is separate, so
`config()` finds function `config` and `config` finds constant `config` when
both exist. When only one exists, both forms find it (a bare function name is a
function reference; calling a constant is left to run time), which is more
lenient than PHP, where `strlen` as a bare name is an undefined constant.

Inside a class whose members are lexically visible
([`ClassScope::Lexical`](#classscope)), the class's inherited members come
between its own members and the enclosing scopes: a base's member shadows a
module item of the same name, and a local or the class's own member shadows the
base's. Inherited members are only known once every base is resolved, so such a
name is resolved as if nothing were inherited, set aside, and finished in phase
4: the first member in [method resolution order](#classes-members-and-mixins)
that the class may use (a base's `private` member is not inherited, so the
search goes on past it) wins; with none, the set-aside outcome stands. The
class header (its bases, interfaces, and mixin uses) never sees inherited
members: it names them.

### Paths and partial resolution

Past the first segment, a path steps through containers:

- a **module** of the program: its final table, with access checked;
- a **sum** of the program: its variant (a variant cannot be a prefix);
- a **class or interface** of the program: its member table after mixins (in
  phase 4); a member not found is left to type-directed resolution;
- a **container outside the program** (module or extern): [`Env::member`](#env);
- anything else that can carry members (a record, an alias, a type parameter, a
  primitive, an extern that does not know the member): the rest is left
  *type-directed*, `resolve_partial(path, res, remaining)`.

A path through a function, constant, global, variant, or local is
[`NotAContainer`](#diagkind). A full resolution must also fit the path's
namespace (HIR spec §3.3), or it is [`WrongKind`](#diagkind).

Roots: `::` starts at the unit's root module (then roots); `self::` at the
current module; `super::` *n* modules up (past the root is
[`SuperBeyondRoot`](#diagkind)). `self::`, `parent::`, and `static::` follow the
policy's [`RootBinding`](#rootbinding): early binding looks the first segment up
in the enclosing class (or its first base), late binding leaves the whole path
type-directed. A qualified self `<T as Tr>::x` resolves `Tr` and leaves the rest.

### Imports as a fixpoint

Every (scope, namespace, name) slot moves up a lattice: absent, one binding,
ambiguous. A named import's slot copies the slot its path reaches (ambiguous if
any step is); a glob joins every visible slot of its target (two different
meanings join to ambiguous; the same meaning reached twice is one binding, with
the wider visibility). Every rule is monotone, so the result is the least
fixpoint, independent of declaration order. It is computed by a worklist:
imports waiting on an absent slot are woken when it fills; resolved imports are
re-evaluated when a slot they read changes.

Two cases cannot be decided by monotonicity alone, and are documented
compromises:

- A **lexical first segment** that misses in a scope with globs may later be
  provided by a glob, which would shadow an outer scope, a root, or the prelude.
  Such imports wait. When nothing else can move, each wait is *glob-blocked*
  (only a glob could still fill the slot) or *import-blocked* (a waiting named
  import binds the name). A name is *producible* while a waiting named import
  of that name, or any waiting glob, could still create a slot for it; new
  slots come from nowhere else. The worklist then settles, in this order:
  1. the lowest-numbered glob-blocked import waiting on an unproducible name,
     in *exact final mode*: a miss in a scope with globs counts as absent only
     for an unproducible name (a producible one is still waited for), so its
     fallback is the one the finished tables give;
  2. otherwise the lowest-numbered glob-blocked import, in *forced final mode*
     (every such miss counts as absent);
  3. only when every wait is import-blocked (a true cycle), the
     lowest-numbered one, in *cycle mode*, where a name a waiting import binds
     is an [`ImportCycle`](#diagkind).

  In the two final modes a name a waiting named import binds is still waited
  for. Imports settled in a final mode are checked again at the end and
  reported as [`ImportAmbiguity`](#diagkind) if the finished tables would
  resolve them differently. A differential test (`tests/import_corner.rs`)
  holds this to a naive fixpoint on random graphs of relative imports whose
  first segment arrives only through globs, under isolated and lexical module
  scoping.
- A **glob import** whose module path turns ambiguous after it has copied names
  keeps what it copied (retracting would break monotonicity) and is reported as
  [`ImportAmbiguity`](#diagkind).

A named import never resolves through itself (`import os` looks past its own
binding of `os`), and a named import shadows what a glob would bring under its
name. An import that binds several tables (a name that is both a function and a
module, say) resolves its path to the first table in the order value, type,
module, macro, constant that holds one meaning, whichever filled first. Names
that remain absent are [`Unresolved`](#diagkind);
imports waiting on each other are [`ImportCycle`](#diagkind); a name bound by a
failed import is [`BrokenImport`](#diagkind) where it is used.

### Bare identifier patterns

A `Pat::Ident` is a bare identifier whose meaning resolve-lang decides (HIR spec
§6): if its name resolves to a constant, a unit variant, or a unit record, the
path is resolved to it and the pattern matches that value; otherwise the path is
left `Res::Unresolved` and the pattern binds its binder. Neither case is a
diagnostic. [`ResolvedUnit::ident_binds`](#resolvedunit) answers which.

### Classes, members, and mixins

Each class and interface has a member table: its own members, then what its
mixins (PHP traits, `ItemKind::MixinUse`) contribute. For each mixin use, every
mixin member is added unless an `insteadof` rule excludes it or the class
defines it; two mixins contributing different members of one name without an
`insteadof` is a [`MixinConflict`](#diagkind) (the first is kept); `m as n`
adds an alias, `m as protected` changes visibility. Mixins that use mixins are
expanded first; a cycle is [`MixinCycle`](#diagkind).

Inherited lookups follow the **C3 method resolution order** (Python's): a class
`C` with bases `B1 … Bn` (`supers` for interfaces) has the order `C` followed by
the merge of `L(B1) … L(Bn)` and the list `B1 … Bn`, taking at each step the
first head that is in no list's tail. One base `B` gives `C, L(B)`, so long
single-inheritance chains are walked directly and memoized. Classes with
several bases are linearized once, eagerly, bases first, without recursion. When
no head qualifies the hierarchy is inconsistent (a base listed before a class
derived from it, a repeated base, contradictory orders): that is
[`InconsistentMro`](#diagkind), as Python raises `TypeError` at class creation,
and the class falls back to its bases' orders concatenated left to right
without repeats, so member lookup still answers. A base outside the program is a
leaf (the environment answers for its ancestors); a base still being linearized
(an inheritance cycle) is a leaf too, so every class gets an order.

Private members are accessible inside the class that holds them; protected
members inside any class related by inheritance. Unqualified access to members
follows [`ClassScope`](#classscope).

### Case folding

A [`Case`](#case) is set per table. A case-insensitive table compares names
after mapping ASCII `A`-`Z` to `a`-`z`; every other byte must match. Every
lookup goes through the table's key, so the rule holds for unqualified names,
module-qualified paths, imports, class members, mixin rules (`HELLO as greet`
names method `Hello`), unit root names, and duplicate detection (`function foo`
and `function FOO` in one scope are a [`Duplicate`](#diagkind)). Names are kept
as written everywhere a tool sees them: diagnostics, [`ClassMember`](#classmember)
names, the [`Index`](#index). A [`rename_set`](#index) includes references
spelled in another case (`GREET()` for `function Greet`), except ones through an
aliased import, which spell the alias.

The fold maps each symbol to the canonical symbol of its case class (the
lowercase spelling if the interner has it, else the lowest-numbered spelling),
which is fixed by the interner, so results do not depend on visiting order.
With any case-insensitive table, resolution first passes once over the
interner's symbols (allocating only for those with an ASCII capital); without
one, folding is free. Names the [`Env`](#env) is asked for are passed as
written: an environment serving a case-insensitive table matches them
case-insensitively itself.

### What every path ends as

| Outcome | `res` | Diagnostics |
|---|---|---|
| Resolved | the binder or definition, `unresolved` = type-directed rest | none |
| Resolved, but not accessible here | the definition | exactly one `Private` |
| Not resolvable | `Res::Err` | exactly one |
| Already resolved (or `Err`) on input | unchanged | none (it is still indexed) |
| Bare identifier pattern that binds | `Res::Unresolved` | none |
| Late-bound or not statically known (`static::x`, an unknown member) | `Res::Unresolved`, all or part type-directed | none |

## `resolve`

```rust,ignore
pub fn resolve<L: intern_lang::Lookup>(hir: Hir, names: &L) -> Result<Resolution, ResolveError>
```

Resolves one unit with [`Policy::new`](#policynew), no environment
([`NoEnv`](#noenv)), and [`Budget::default`](#budget). `names` is the interner
the unit's names came from; it is read only to compare spellings for
suggestions.

| Parameter | Meaning |
|---|---|
| `hir` | The unit, taken by value (its resolution slots are filled in place). |
| `names` | Any `intern_lang::Lookup` (`Interner` or `ConcurrentInterner`). |

**Errors:** [`ResolveError::BudgetExceeded`](#resolveerror). Name errors in the
program are diagnostics in the result.

```rust
use hir_lang::{Builder, Name};
use intern_lang::Interner;

let mut names = Interner::new();
let mut b = Builder::new();
let ghost = b.name_expr(Name::new(names.intern("ghost")));
let body = b.block(&[], Some(ghost));
let f = b.func(Name::new(names.intern("f")), &[], body);
let root = b.module(None, &[f]);
let res = resolve_lang::resolve(b.finish(root)?, &names)?;
assert_eq!(res.diagnostics().len(), 1);
assert!(res.diagnostics()[0].kind.is_unresolved());
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `Policy`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Policy { /* private */ }
impl Default for Policy {}
```

A language's scoping rules as data. All constructors and setters are `const fn`.

### `Policy::new`

```rust,ignore
pub const fn new() -> Policy
```

The lexical default, equal to [`kraken`](#policykraken):

| Setting | Value |
|---|---|
| Hoisting | every item class: [`Hoist::Scope`](#hoist) |
| Namespaces | value, type, macro, label tables; modules share the type table, constants the value table |
| Case | every table case-sensitive |
| Occupies | functions, globals: value; constants: constant; records, classes: type and value; sums, interfaces, aliases, associated types: type; modules: module |
| Shadowing | [`Allow`](#shadowing) |
| Redefinition | [`Error`](#redefinition) |
| Class scope | [`Lexical`](#classscope) (own and inherited members) |
| Module scope | [`Isolated`](#modulescope) |
| Roots | `self::` early; `parent::`, `static::` unsupported |
| Visibility | enforced; private items visible in descendant modules |
| Imports | globs and aliases allowed; re-export [`AsDeclared`](#reexport) |
| `global` declarations | must name a known global |

```rust
use resolve_lang::{ClassScope, Hoist, ItemClass, Policy};

let p = Policy::new();
assert_eq!(p.hoisting(ItemClass::Fn), Hoist::Scope);
assert_eq!(p.class_scope(), ClassScope::Lexical);
assert_eq!(p, Policy::default());
```

### `Policy::kraken`

```rust,ignore
pub const fn kraken() -> Policy
```

Kraken and Iron: lexical scoping, modules, imports, visibility. Equal to `new`.

```rust
use resolve_lang::Policy;

assert_eq!(Policy::kraken(), Policy::new());
```

### `Policy::php`

```rust,ignore
pub const fn php() -> Policy
```

PHP and Mox: functions, records, sums, classes, interfaces, and constants are
[`Hoist::Module`](#hoist) (visible in their whole namespace wherever declared,
conditional declarations included); class members only through
`self::`/`parent::`/`static::` ([`ClassScope::Qualified`](#classscope));
`self::` and `parent::` early, `static::` late; nested namespaces see outer
names; no glob imports; imports never re-export; `global $x` may name a global
that does not exist yet (it binds `Res::Extern`). Names follow PHP 8's tables
and case rules:

| Table | Holds | Case |
|---|---|---|
| value | functions, methods | ASCII-insensitive |
| type (with module) | classes, interfaces, traits, enums, namespaces | ASCII-insensitive |
| constant | constants, class constants, globals, static properties | sensitive |

So a function and a constant, or a method and a class constant, may share a
name (not a [`Duplicate`](#diagkind)); `strlen()` and `STRLEN()` are one
function; `FOO` and `foo` are two constants; and a class is a type only
(construct it through a type path, as `new C` lowers). HIR paths carry no `$`
sigil, so a sketch that strips it from static property names makes a static
property and a class constant of one name collide: keep the sigil in property
names (`$count`).

```rust
use resolve_lang::{Case, ClassScope, Hoist, ItemClass, Namespace, NsSet, Policy, RootBinding};

let p = Policy::php();
assert_eq!(p.hoisting(ItemClass::Fn), Hoist::Module);
assert_eq!(p.class_scope(), ClassScope::Qualified);
assert_eq!(p.static_root(), RootBinding::Late);
assert!(!p.globs_allowed());
assert_eq!(p.case(Namespace::Value), Case::AsciiInsensitive);
assert_eq!(p.case(Namespace::Const), Case::Sensitive);
assert_eq!(p.occupies(ItemClass::Class), NsSet::single(Namespace::Type));
assert_ne!(p.table(Namespace::Const), p.table(Namespace::Value));
```

### `Policy::python`

```rust,ignore
pub const fn python() -> Policy
```

Python and Mercury: one case-sensitive table for every name; scope hoisting (a
name bound anywhere in a scope belongs to the whole scope); class bodies visible
to their own initializers but not to methods
([`ClassScope::BodyOnly`](#classscope)); members inherited in C3 order, an
inconsistent hierarchy reported ([`InconsistentMro`](#diagkind)); redefinition
rebinds ([`LastWins`](#redefinition)); visibility not enforced; imports always
re-export; no type-relative roots; implicit globals.

```rust
use resolve_lang::{ClassScope, Namespace, Policy, Redefinition};

let p = Policy::python();
assert_eq!(p.table(Namespace::Type), Namespace::Value);
assert_eq!(p.class_scope(), ClassScope::BodyOnly);
assert_eq!(p.redefinition(), Redefinition::LastWins);
```

### Policy setters

Each takes the policy by value and returns the changed policy.

| Setter | Parameters | Effect |
|---|---|---|
| `with_hoisting(class, hoist)` | [`ItemClass`](#itemclass), [`Hoist`](#hoist) | When items of `class` become visible. `Hoist::Module` never moves class members out of their class. |
| `with_occupies(class, set)` | [`ItemClass`](#itemclass), [`NsSet`](#nsset) | The namespaces items of `class` define their name in. Imports ignore it (they bind what their target defines). |
| `with_merge(from, into)` | two [`Namespace`](#namespace)s | `from` (and everything already merged with it) shares `into`'s table, which keeps `into`'s case. |
| `with_case(ns, case)` | [`Namespace`](#namespace), [`Case`](#case) | How the table of `ns` (and everything merged with it) compares names. Merge first, then set the case. |
| `with_shadowing(rule)` | [`Shadowing`](#shadowing) | Whether binders may reuse visible names. |
| `with_redefinition(rule)` | [`Redefinition`](#redefinition) | What two definitions of a name in one scope mean. |
| `with_class_scope(rule)` | [`ClassScope`](#classscope) | What code in a class sees of its members unqualified. |
| `with_module_scope(rule)` | [`ModuleScope`](#modulescope) | Whether nested modules see outer names. |
| `with_roots(self_, parent, static_)` | three [`RootBinding`](#rootbinding)s | How `self::`, `parent::`, `static::` bind. |
| `with_visibility(enforce, private_to_descendants)` | two `bool`s | Whether `Vis` is enforced; whether private items are visible in descendant modules. |
| `with_imports(globs, aliases, reexport)` | `bool`, `bool`, [`Reexport`](#reexport) | Which import forms exist; how imports re-export. |
| `with_implicit_globals(yes)` | `bool` | Whether an unknown `global` name binds a host global. |

```rust
use resolve_lang::{
    ClassScope, Hoist, ItemClass, ModuleScope, Namespace, NsSet, Policy, Redefinition, Reexport,
    RootBinding, Shadowing,
};

let p = Policy::new()
    .with_hoisting(ItemClass::Fn, Hoist::AfterDecl)
    .with_occupies(ItemClass::Record, NsSet::single(Namespace::Type))
    .with_merge(Namespace::Macro, Namespace::Value)
    .with_case(Namespace::Type, resolve_lang::Case::AsciiInsensitive)
    .with_shadowing(Shadowing::DenySameScope)
    .with_redefinition(Redefinition::LastWins)
    .with_class_scope(ClassScope::Qualified)
    .with_module_scope(ModuleScope::Lexical)
    .with_roots(RootBinding::Early, RootBinding::Early, RootBinding::Late)
    .with_visibility(true, false)
    .with_imports(true, false, Reexport::Never)
    .with_implicit_globals(true);
assert_eq!(p.hoisting(ItemClass::Fn), Hoist::AfterDecl);
assert_eq!(p.table(Namespace::Macro), Namespace::Value);
assert_eq!(p.case(Namespace::Module), resolve_lang::Case::AsciiInsensitive);
assert!(!p.aliases_allowed());
```

### Policy getters

| Getter | Returns |
|---|---|
| `hoisting(class)` | [`Hoist`](#hoist) |
| `occupies(class)` | [`NsSet`](#nsset) (before merging) |
| `table(ns)` | the [`Namespace`](#namespace) whose table `ns` is stored in |
| `case(ns)` | the [`Case`](#case) of that table |
| `shadowing()`, `redefinition()`, `class_scope()`, `module_scope()` | the rule |
| `self_root()`, `parent_root()`, `static_root()` | [`RootBinding`](#rootbinding) |
| `visibility_enforced()`, `private_to_descendants()` | `bool` |
| `globs_allowed()`, `aliases_allowed()`, `reexport()` | `bool`, `bool`, [`Reexport`](#reexport) |
| `implicit_globals()` | `bool` |

```rust
use resolve_lang::{ItemClass, ModuleScope, Namespace, Policy, Reexport, RootBinding, Shadowing};

let p = Policy::kraken();
assert!(p.occupies(ItemClass::Record).contains(Namespace::Value));
assert_eq!(p.table(Namespace::Module), Namespace::Type);
assert_eq!(p.shadowing(), Shadowing::Allow);
assert_eq!(p.module_scope(), ModuleScope::Isolated);
assert_eq!((p.self_root(), p.parent_root()), (RootBinding::Early, RootBinding::Unsupported));
assert!(p.visibility_enforced() && p.private_to_descendants());
assert_eq!(p.reexport(), Reexport::AsDeclared);
assert!(!p.implicit_globals());
```

## `Namespace`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Namespace { Value, Type, Module, Macro, Label, Const }
impl Namespace {
    pub const ALL: [Namespace; 6];
    pub const fn name(self) -> &'static str;
}
```

The tables names live in. HIR has no macro items or label paths: those
namespaces exist for merging rules and for names the environment exports.
`Const` holds constants (and, under [`Policy::php`](#policyphp), globals and
static properties); it is merged into `Value` unless the policy keeps it apart,
and value paths search it before or after the value table depending on whether
they are a call's callee (see [Lexical lookup](#lexical-lookup)).

```rust
use resolve_lang::Namespace;

assert_eq!(
    Namespace::ALL.map(Namespace::name),
    ["value", "type", "module", "macro", "label", "constant"]
);
```

## `NsSet`

```rust,ignore
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct NsSet { /* private */ }
impl NsSet {
    pub const EMPTY: NsSet;
    pub const fn of(namespaces: &[Namespace]) -> NsSet;
    pub const fn single(ns: Namespace) -> NsSet;
    pub const fn contains(self, ns: Namespace) -> bool;
    pub const fn is_empty(self) -> bool;
    pub const fn with(self, ns: Namespace) -> NsSet;
    pub fn iter(self) -> impl Iterator<Item = Namespace>;
}
```

A set of namespaces (a bit set), for [`Policy::with_occupies`](#policy-setters).

```rust
use resolve_lang::{Namespace, NsSet};

let s = NsSet::EMPTY.with(Namespace::Type).with(Namespace::Value);
assert_eq!(s, NsSet::of(&[Namespace::Value, Namespace::Type]));
assert!(s.contains(Namespace::Type) && !s.is_empty());
assert_eq!(s.iter().collect::<Vec<_>>(), [Namespace::Value, Namespace::Type]);
assert!(NsSet::single(Namespace::Module).contains(Namespace::Module));
```

## `Case`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Case { Sensitive, AsciiInsensitive }
```

How a table compares names (see [Case folding](#case-folding)).
`AsciiInsensitive` is PHP 8's rule: ASCII letters fold, every other byte
(UTF-8 included) must match. Unicode case folding is not offered: no target
language needs it, and its tables change with the Unicode version, which would
make resolution depend on the toolchain.

```rust
use resolve_lang::{Case, Namespace, Policy};

let p = Policy::new().with_case(Namespace::Value, Case::AsciiInsensitive);
assert_eq!(p.case(Namespace::Value), Case::AsciiInsensitive);
assert_eq!(p.case(Namespace::Type), Case::Sensitive);
```

## `ItemClass`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ItemClass { Fn, Record, Sum, Class, Interface, Alias, AssocType, Const, Global, Module, Import }
impl ItemClass {
    pub const ALL: [ItemClass; 11];
    pub const fn of(kind: &hir_lang::ItemKind) -> Option<ItemClass>;
}
```

The kinds of named items the policy distinguishes. `of` is `None` for items
that bind no name (`impl`, mixin use, error items).

```rust
use hir_lang::{ItemKind, SumDef};
use resolve_lang::ItemClass;

assert_eq!(ItemClass::of(&ItemKind::Sum(SumDef::default())), Some(ItemClass::Sum));
assert_eq!(ItemClass::ALL.len(), 11);
```

## `Hoist`

```rust,ignore
pub enum Hoist { Scope, AfterDecl, Module }
```

| Variant | Visible |
|---|---|
| `Scope` | in the whole declaring scope (Rust, Kraken, Python's per-scope rule) |
| `AfterDecl` | from the declaration (itself included, so functions recurse) to the end of the scope |
| `Module` | in the whole enclosing module, wherever declared (PHP) |

```rust
use resolve_lang::{Hoist, ItemClass, Policy};

assert_eq!(Policy::php().hoisting(ItemClass::Class), Hoist::Module);
```

## `Shadowing`

```rust,ignore
pub enum Shadowing { Allow, DenySameScope, DenyLocals }
```

`DenySameScope` reports a binder reusing a name bound earlier in the same scope;
`DenyLocals` one reusing the name of any local visible in the same frame. Each
reported binder gets one [`Shadowing`](#diagkind) diagnostic (its `node` is
`None`: binders are not nodes; its span is the binder's).

```rust
use resolve_lang::{Policy, Shadowing};

assert_eq!(Policy::new().shadowing(), Shadowing::Allow);
```

## `Redefinition`

```rust,ignore
pub enum Redefinition { Error, LastWins }
```

`Error` keeps the first definition and reports each later one as
[`Duplicate`](#diagkind) (one diagnostic per item, however many namespaces it
occupies). `LastWins` keeps all: static lookups see the last, and with
`AfterDecl` each is visible from its own declaration.

```rust
use resolve_lang::{Policy, Redefinition};

assert_eq!(Policy::python().redefinition(), Redefinition::LastWins);
```

## `ClassScope`

```rust,ignore
pub enum ClassScope { Lexical, BodyOnly, Qualified }
```

| Variant | Class members unqualified |
|---|---|
| `Lexical` | everywhere in the class body, methods included: its own members, then inherited ones in C3 order (not a base's private members), then the enclosing scopes |
| `BodyOnly` | in the class body and its constant/global initializers, not in methods, lambdas, or nested classes (Python) |
| `Qualified` | never (PHP: `self::x`, `$this->x`) |

```rust
use resolve_lang::{ClassScope, Policy};

assert_eq!(Policy::python().class_scope(), ClassScope::BodyOnly);
```

## `ModuleScope`

```rust,ignore
pub enum ModuleScope { Isolated, Lexical }
```

`Isolated`: a nested module starts a fresh lexical world (reach outer items with
`super::` or an import). `Lexical`: it sees the names around it.

```rust
use resolve_lang::{ModuleScope, Policy};

assert_eq!(Policy::kraken().module_scope(), ModuleScope::Isolated);
assert_eq!(Policy::php().module_scope(), ModuleScope::Lexical);
```

## `RootBinding`

```rust,ignore
pub enum RootBinding { Early, Late, Unsupported }
```

`Early`: `self::x` is looked up in the enclosing class (`parent::x` in its first
base); a member found is resolved now, one not found is left type-directed.
`Late`: the whole path is type-directed. `Unsupported`: reported as
[`RootUnsupported`](#diagkind). Inside an `impl` block every type-relative path
is type-directed; outside any class, interface, or impl it is
[`OutsideType`](#diagkind).

```rust
use resolve_lang::{Policy, RootBinding};

assert_eq!(Policy::php().parent_root(), RootBinding::Early);
```

## `Reexport`

```rust,ignore
pub enum Reexport { AsDeclared, Always, Never }
```

How an import's own `Vis` decides whether other modules see it: as declared
(`pub use`), always (Python), never (PHP).

```rust
use resolve_lang::{Policy, Reexport};

assert_eq!(Policy::php().reexport(), Reexport::Never);
```

## `Env`

```rust,ignore
pub trait Env {
    fn root(&self, name: Name) -> Option<Export> { None }
    fn prelude(&self, name: Name, ns: Namespace) -> Option<Export> { None }
    fn member(&self, container: Res, name: Name, ns: Namespace) -> Option<Export> { None }
    fn for_each_member(&self, container: Res, f: &mut dyn FnMut(Name, Namespace, Export)) {}
    fn for_each_root(&self, f: &mut dyn FnMut(Name)) {}
    fn for_each_prelude(&self, f: &mut dyn FnMut(Name, Namespace)) {}
}
```

The host's side: names outside the program. Every method has a do-nothing
default.

| Method | Called for |
|---|---|
| `root` | the first segment of a longer path or of an import, after lexical scopes and the program's unit roots |
| `prelude` | any first segment, after everything else |
| `member` | a segment after a container outside the program (`Res::Def` of another package, `Res::Extern`) |
| `for_each_member` | a glob import of an outside container; a mixin outside the program |
| `for_each_root`, `for_each_prelude` | did-you-mean candidates (collected once per unit) |

Members of outside *classes* (`Other::member`) are asked through `member` with
the class as container; the environment answers inherited members itself.

```rust
use hir_lang::{Name, Prim, Res};
use resolve_lang::{DefKind, Env, Export, Namespace};

struct Prims { int: Name }

impl Env for Prims {
    fn prelude(&self, name: Name, ns: Namespace) -> Option<Export> {
        (name == self.int && ns == Namespace::Type).then(|| Export::new(Res::Prim(Prim::I64), DefKind::Prim))
    }
}

let mut names = intern_lang::Interner::new();
let env = Prims { int: Name::new(names.intern("int")) };
assert!(env.prelude(env.int, Namespace::Type).is_some());
assert!(env.root(env.int).is_none());
```

## `Export`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Export { pub res: Res, pub kind: DefKind, pub vis: Vis }
impl Export {
    pub const fn new(res: Res, kind: DefKind) -> Export;   // vis: Public
    pub const fn with_vis(self, vis: Vis) -> Export;
}
```

A name the environment exports. A non-`Public` export reached from the program is
resolved and reported as [`Private`](#diagkind) (when visibility is enforced).

```rust
use hir_lang::{Res, Symbol, Vis};
use resolve_lang::{DefKind, Export};

let e = Export::new(Res::Extern(Symbol::from_u32(1).unwrap()), DefKind::Extern).with_vis(Vis::Package);
assert_eq!(e.vis, Vis::Package);
```

## `DefKind`

```rust,ignore
#[non_exhaustive]
pub enum DefKind {
    Module, Fn, Const, Global, Record { unit: bool }, Sum, Class { mixin: bool },
    Interface, Alias, AssocType, Variant { unit: bool }, Extern, Prim, Local, Err,
}
impl DefKind {
    pub const fn of_item(kind: &ItemKind) -> Option<DefKind>;
    pub const fn fits(self, ns: Ns) -> bool;
    pub const fn is_prefix(self) -> bool;
    pub const fn is_pattern_constant(self) -> bool;
    pub const fn name(self) -> &'static str;
}
```

What a resolution names, as far as scoping cares. `fits` mirrors HIR spec §3.3
(which namespaces may name it); `is_prefix` whether a path may continue past it;
`is_pattern_constant` whether a bare identifier pattern naming it matches rather
than binds. `Local` appears only in diagnostics.

```rust
use hir_lang::{ItemKind, Ns};
use resolve_lang::DefKind;

assert!(DefKind::Variant { unit: true }.fits(Ns::Pattern));
assert!(DefKind::Variant { unit: true }.is_pattern_constant());
assert!(!DefKind::Fn.is_prefix());
assert_eq!(DefKind::of_item(&ItemKind::Err), Some(DefKind::Err));
assert_eq!(DefKind::Class { mixin: true }.name(), "mixin");
```

## `NoEnv`

```rust,ignore
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NoEnv;
impl Env for NoEnv {}
```

The empty environment ([`resolve`](#resolve) uses it).

```rust
use hir_lang::{Name, Symbol};
use resolve_lang::{Env, Namespace, NoEnv};

assert!(NoEnv.prelude(Name::new(Symbol::from_u32(1).unwrap()), Namespace::Value).is_none());
```

## `MapEnv`

```rust,ignore
#[derive(Clone, Debug, Default)]
pub struct MapEnv { /* private */ }
impl MapEnv {
    pub fn new() -> MapEnv;
    pub fn with_root(self, name: Name, export: Export) -> MapEnv;
    pub fn with_prelude(self, name: Name, ns: Namespace, export: Export) -> MapEnv;
    pub fn with_member(self, container: Res, name: Name, ns: Namespace, export: Export) -> MapEnv;
}
impl Env for MapEnv {}
```

A ready-made in-memory environment. Lookups are `O(log n)`; enumeration is in
name order. `with_member` ignores containers that are not `Res::Def` or
`Res::Extern`. Registering a name twice keeps the later export.

```rust
use hir_lang::{Name, Res};
use intern_lang::Interner;
use resolve_lang::{DefKind, Env, Export, MapEnv, Namespace};

let mut names = Interner::new();
let (os, getcwd) = (names.intern("os"), names.intern("getcwd"));
let env = MapEnv::new()
    .with_root(Name::new(os), Export::new(Res::Extern(os), DefKind::Module))
    .with_member(Res::Extern(os), Name::new(getcwd), Namespace::Value, Export::new(Res::Extern(getcwd), DefKind::Extern));
let root = env.root(Name::new(os)).unwrap();
assert_eq!(env.member(root.res, Name::new(getcwd), Namespace::Value).map(|e| e.res), Some(Res::Extern(getcwd)));
```

## `Resolver`

```rust,ignore
#[derive(Clone, Copy)]
pub struct Resolver<'e> { /* private */ }
impl Resolver<'static> { pub fn new(policy: Policy) -> Resolver<'static>; }
impl Resolver<'_> {
    pub fn with_env(self, env: &dyn Env) -> Resolver<'_>;
    pub fn with_budget(self, budget: Budget) -> Self;
    pub fn resolve<L: Lookup>(self, hir: Hir, names: &L) -> Result<Resolution, ResolveError>;
}
```

One unit with a policy, an environment, and a budget (the configured path). A
unit resolved alone has no root name.

**Errors:** [`ResolveError::BudgetExceeded`](#resolveerror).

```rust
use hir_lang::{Builder, Name, Res};
use intern_lang::Interner;
use resolve_lang::{Budget, DefKind, Export, MapEnv, Namespace, Policy, Resolver};

let mut names = Interner::new();
let echo = Name::new(names.intern("echo"));
let env = MapEnv::new().with_prelude(echo, Namespace::Value, Export::new(Res::Extern(echo.sym), DefKind::Extern));
let mut b = Builder::new();
let e = b.name_expr(echo);
let body = b.block(&[], Some(e));
let main = b.func(Name::new(names.intern("main")), &[], body);
let root = b.module(None, &[main]);

let res = Resolver::new(Policy::php())
    .with_env(&env)
    .with_budget(Budget::default())
    .resolve(b.finish(root)?, &names)?;
assert!(res.is_clean());
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `Program`

```rust,ignore
pub struct Program<'e> { /* private */ }
impl Program<'static> { pub fn new(policy: Policy) -> Program<'static>; }
impl Program<'_> {
    pub fn with_env(self, env: &dyn Env) -> Program<'_>;
    pub fn with_budget(self, budget: Budget) -> Self;
    pub fn add_unit(&mut self, name: Option<Name>, hir: Hir);
    pub fn add_unit_in(&mut self, package: u32, name: Option<Name>, hir: Hir);
    pub fn len(&self) -> usize;
    pub fn is_empty(&self) -> bool;
    pub fn resolve<L: Lookup>(self, names: &L) -> Result<Resolution, ResolveError>;
}
```

The in-memory multi-unit driver (the power path). Units resolve against each
other: definitions of other units are `Res::Def` with their `UnitId`s, imports
may form cycles across units, and the index spans the program. A unit added with
a name is reachable from every unit as a path's first segment; if two units claim
one name, the first added keeps it. `add_unit` puts the unit in package 0;
`Vis::Package` items are visible across units of the same package only.

**Errors:** [`ResolveError::DuplicateUnit`](#resolveerror) if two units share a
`UnitId`; [`ResolveError::BudgetExceeded`](#resolveerror).

```rust
use hir_lang::{Builder, FnDef, Item, ItemKind, Name, Ns, Path, Segment, UnitId, Vis};
use intern_lang::Interner;
use resolve_lang::{Policy, Program};

/// `use <other>::<import>;  pub fn <define>() { <import> }`
fn unit(id: u32, other: Name, import: Name, define: Name) -> Result<hir_lang::Hir, hir_lang::HirError> {
    let mut b = Builder::for_unit(UnitId::new(id));
    let segs = [Segment::new(other, b.origin()), Segment::new(import, b.origin())];
    let segs = b.list(&segs);
    let path = b.path(Path::new(segs, Ns::Import));
    let imp = b.item(Item::new(None, ItemKind::Import { path, glob: false }));
    let call = b.name_expr(import);
    let body = b.block(&[], Some(call));
    let f = b.item(Item::new(Some(define), ItemKind::Fn(FnDef { body: Some(body), ..FnDef::default() })).with_vis(Vis::Public));
    let root = b.module(None, &[imp, f]);
    b.finish(root)
}

let mut names = Interner::new();
let (a, b) = (Name::new(names.intern("a")), Name::new(names.intern("b")));
let (ping, pong) = (Name::new(names.intern("ping")), Name::new(names.intern("pong")));
let mut program = Program::new(Policy::kraken());
program.add_unit(Some(a), unit(1, b, pong, ping)?);   // a: use b::pong
program.add_unit(Some(b), unit(2, a, ping, pong)?);   // b: use a::ping
assert_eq!(program.len(), 2);
let res = program.resolve(&names)?;
assert!(res.is_clean());
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `Resolution`

```rust,ignore
#[derive(Clone, Debug)]
pub struct Resolution { /* private */ }
impl Resolution {
    pub fn units(&self) -> &[ResolvedUnit];
    pub fn unit(&self, id: UnitId) -> Option<&ResolvedUnit>;
    pub fn hir(&self, id: UnitId) -> Option<&Hir>;
    pub fn diagnostics(&self) -> &[Diagnostic];
    pub fn is_clean(&self) -> bool;
    pub fn index(&self) -> &Index;
    pub fn into_parts(self) -> (Vec<ResolvedUnit>, Vec<Diagnostic>, Index);
}
```

The result. Units are in the order added. Diagnostics are sorted by unit (in
that order), then by span start and end, then by discovery.

```rust
use hir_lang::{Builder, UnitId};
use intern_lang::Interner;

let mut b = Builder::for_unit(UnitId::new(5));
let root = b.module(None, &[]);
let res = resolve_lang::resolve(b.finish(root)?, &Interner::new())?;
assert!(res.unit(UnitId::new(5)).is_some() && res.hir(UnitId::new(5)).is_some());
assert!(res.is_clean() && res.diagnostics().is_empty());
assert!(res.index().definitions().is_empty());
let (units, diagnostics, _index) = res.into_parts();
assert_eq!((units.len(), diagnostics.len()), (1, 0));
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `ResolvedUnit`

```rust,ignore
#[derive(Clone, Debug)]
pub struct ResolvedUnit { /* private */ }
impl ResolvedUnit {
    pub fn id(&self) -> UnitId;
    pub fn name(&self) -> Option<Name>;
    pub fn hir(&self) -> &Hir;
    pub fn into_hir(self) -> Hir;
    pub fn members(&self, class: ItemId) -> Option<&[ClassMember]>;
    pub fn ident_binds(&self, pat: PatId) -> Option<bool>;
}
```

One resolved unit. `hir` is a valid `Hir` with every resolvable slot filled.
`members` is the effective member table of a class or interface item (own
members plus mixin contributions), sorted by namespace, then name symbol.
`ident_binds` answers, for a `Pat::Ident`, whether it binds (`Some(true)`) or
matches a constant (`Some(false)`).

```rust
use hir_lang::{Builder, ClassDef, Item, ItemKind, Name};
use intern_lang::Interner;

let mut names = Interner::new();
let mut b = Builder::new();
let body = b.block(&[], None);
let m = b.func(Name::new(names.intern("m")), &[], body);
let items = b.list(&[m]);
let class = b.item(Item::new(Some(Name::new(names.intern("C"))), ItemKind::Class(ClassDef { items, ..ClassDef::default() })));
let root = b.module(None, &[class]);
let res = resolve_lang::resolve(b.finish(root)?, &names)?;
let unit = &res.units()[0];
assert_eq!(unit.members(class).unwrap()[0].name, Name::new(names.intern("m")));
assert!(unit.members(m).is_none());
assert!(unit.name().is_none());
let hir = unit.clone().into_hir();
assert!(hir.validate().is_ok());
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `ClassMember`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClassMember {
    pub name: Name,             // the name in this class as written (an alias's new name)
    pub namespace: Namespace,   // its table, after merging
    pub res: Res,               // what it resolves to (a mixin member: the mixin's item)
    pub vis: Vis,               // its visibility here (a rule may change it)
    pub mixin: Option<DefId>,   // the mixin it came from, or None for an own member
}
```

```rust
use hir_lang::{Name, Res, Symbol, Vis};
use resolve_lang::{ClassMember, Namespace};

let m = ClassMember { name: Name::new(Symbol::from_u32(1).unwrap()), namespace: Namespace::Value, res: Res::Err, vis: Vis::Protected, mixin: None };
assert_eq!(m.vis, Vis::Protected);
```

## `Diagnostic`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Diagnostic { pub kind: DiagKind, pub unit: UnitId, pub span: Span, pub node: Option<NodeRef> }
impl Diagnostic { pub fn message<L: Lookup>(&self, names: &L) -> String; }
```

One problem. `span` is the offending name's span (a path segment, an item's name,
a binder); `node` the path or item it is about. `message` renders one English
line, spelling names through `names` (`?` for a symbol `names` does not know).

```rust
use hir_lang::{Span, UnitId};
use intern_lang::Interner;
use resolve_lang::{DiagKind, Diagnostic};

let d = Diagnostic { kind: DiagKind::GlobsUnsupported, unit: UnitId::new(0), span: Span::new(0, 5), node: None };
assert_eq!(d.message(&Interner::new()), "glob imports are not supported by this language");
```

## `DiagKind`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum DiagKind { /* variants below */ }
impl DiagKind {
    pub const fn is_unresolved(&self) -> bool;
    pub const fn suggestion(&self) -> Option<Name>;
}
```

| Variant | Meaning | Message |
|---|---|---|
| `Unresolved { name, ns, container, suggestion }` | Not visible (or, with `container`, not defined there). `suggestion`: the closest visible name within distance `max(1, len/3)`. | ``cannot find value `x` in this scope; did you mean `y`?`` |
| `AmbiguousGlob { name, first, second }` | Two glob imports (or an import through them) give `name` two meanings. | `` `x` is ambiguous: more than one glob import provides it `` |
| `Private { name, res, vis }` | Exists but not accessible here; the path keeps `res`. | `` `x` is private `` |
| `Duplicate { name, first }` | A second definition (or an import colliding with one) in one scope and namespace. | `` `x` is defined more than once in this scope `` |
| `CannotCapture { name, binder }` | A local behind a frame it cannot cross. | ``cannot use local `x` here: it belongs to an enclosing function`` |
| `WrongKind { name, ns, found }` | The name exists but is the wrong kind here (also: found only in another namespace). | ``expected a type, found function `f` `` |
| `NotAContainer { name, found }` | A path continues past something without members. | `` `f` is a function, which has no members `` |
| `Shadowing { name, shadowed }` | A binder the [`Shadowing`](#shadowing) rule forbids. | `` `x` shadows a visible local, which this language forbids `` |
| `BrokenImport { name }` | A name bound by an import that failed. | `` `x` comes from an import that failed to resolve `` |
| `ImportCycle { name }` | An import that depends on itself through other imports. | ``the import of `x` depends on itself`` |
| `ImportAmbiguity { name }` | An import decided before the tables were final turned out ambiguous. | ``the import of `x` is ambiguous with a glob import in the same scope`` |
| `GlobsUnsupported`, `AliasesUnsupported` | An import form the policy does not have. | `glob imports are not supported by this language` |
| `RootUnsupported { root }` | A root the policy does not have, or a type root/qualified self in an import. | ``\`static::\` is not supported here`` |
| `OutsideType { root }` | `self::`/`parent::`/`static::` outside any class, interface, or impl. | |
| `NoParent` | `parent::` in a class without bases. | |
| `SuperBeyondRoot { levels }` | `super::` past the unit's root module. | |
| `MixinConflict { name, first, second }` | Two mixins provide `name`; `first` is kept. | |
| `NotAMixin { found }` | A mixin use names something that is not a mixin. | |
| `UnknownMixinMember { name }` | A mixin rule names a member no used mixin has. | |
| `MixinCycle` | A mixin uses itself. | |
| `InconsistentMro { class }` | A class whose bases admit no C3 order (Python's `TypeError` at class creation); lookups fall back to the bases' orders concatenated without repeats. | ``cannot create a consistent method resolution order (MRO) for the bases of `C` `` |
| `Rejected { error }` | hir-lang refused a resolution resolve-lang computed (a disagreement between the crates; the path is left `Res::Err`). | |

```rust
use hir_lang::{Builder, Name, Ns};
use intern_lang::Interner;
use resolve_lang::DiagKind;

let mut names = Interner::new();
let mut b = Builder::new();
let use_f = b.name_path(Name::new(names.intern("f")), Ns::Type);
let ty = b.ty(hir_lang::Ty::Path(use_f));
let alias = b.item(hir_lang::Item::new(Some(Name::new(names.intern("A"))), hir_lang::ItemKind::Alias { generics: Default::default(), ty }));
let body = b.block(&[], None);
let f = b.func(Name::new(names.intern("f")), &[], body);
let root = b.module(None, &[alias, f]);
let res = resolve_lang::resolve(b.finish(root)?, &names)?;
assert!(matches!(res.diagnostics()[0].kind, DiagKind::WrongKind { ns: Ns::Type, .. }));
assert_eq!(res.diagnostics()[0].message(&names), "expected a type, found function `f`");
assert_eq!(res.diagnostics()[0].kind.suggestion(), None);
# Ok::<(), Box<dyn std::error::Error>>(())
```

## `Budget`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Budget { /* private */ }
impl Default for Budget {}   // 16M glob bindings, 16M member steps, 32M suggestion cells
impl Budget {
    pub const fn unlimited() -> Budget;
    pub const fn with_glob_bindings(self, n: u64) -> Budget;
    pub const fn with_member_steps(self, n: u64) -> Budget;
    pub const fn with_suggestion_cells(self, n: u64) -> Budget;
    pub const fn glob_bindings(&self) -> u64;
    pub const fn member_steps(&self) -> u64;
    pub const fn suggestion_cells(&self) -> u64;
}
```

| Limit | Counts | When spent |
|---|---|---|
| glob bindings | slot changes made by glob propagation | the run fails with `BudgetExceeded { limit: GlobBindings }` |
| member steps | steps of inheritance walks and access checks | the run fails with `BudgetExceeded { limit: MemberSteps }` |
| suggestion cells | edit-distance table cells | suggestions stop; diagnostics continue |

```rust
use resolve_lang::Budget;

let b = Budget::default().with_glob_bindings(1_000).with_member_steps(500).with_suggestion_cells(0);
assert_eq!((b.glob_bindings(), b.member_steps(), b.suggestion_cells()), (1_000, 500, 0));
assert_eq!(Budget::unlimited().glob_bindings(), u64::MAX);
```

## `ResolveError`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ResolveError {
    BudgetExceeded { limit: Limit },
    DuplicateUnit { unit: UnitId },
}
impl Display for ResolveError {}
impl core::error::Error for ResolveError {}
```

Why a run stopped without a result. `BudgetExceeded`: raise the [`Budget`](#budget)
for trusted input, or reject the input. `DuplicateUnit`: give every unit of a
program a distinct `UnitId`.

```rust
use hir_lang::UnitId;
use resolve_lang::{Limit, ResolveError};

let e = ResolveError::BudgetExceeded { limit: Limit::GlobBindings };
assert_eq!(e.to_string(), "resolution exceeded its budget of glob bindings");
let e = ResolveError::DuplicateUnit { unit: UnitId::new(2) };
assert_eq!(e.to_string(), "two units of the program have the id 2");
```

## `Limit`

```rust,ignore
#[non_exhaustive]
pub enum Limit { GlobBindings, MemberSteps }
impl Limit { pub const fn name(self) -> &'static str; }
```

```rust
use resolve_lang::Limit;

assert_eq!(Limit::MemberSteps.name(), "member lookup steps");
```

## `Index`

```rust,ignore
#[derive(Clone, Debug, Default)]
pub struct Index { /* private */ }
impl Index {
    pub fn definitions(&self) -> &[Definition];
    pub fn references_all(&self) -> &[Reference];
    pub fn definition(&self, def: DefRef) -> Option<&Definition>;
    pub fn references(&self, def: DefRef) -> References<'_>;
    pub fn def_of(&self, target: Target) -> Option<DefRef>;
    pub fn resolve_at(&self, unit: UnitId, path: PathId, segment: u32) -> Option<DefRef>;
    pub fn path_references(&self, unit: UnitId, path: PathId) -> &[Reference];
    pub fn at(&self, unit: UnitId, offset: u32) -> Option<Occurrence>;
    pub fn rename_set(&self, def: DefRef) -> RenameSet;
    pub fn document_symbols(&self, unit: UnitId) -> Vec<(DefRef, &Definition)>;
}
```

The persistent definition/reference index of the whole program.

- **Definitions:** every named item, every variant, every binder (except the
  binder of a bare identifier pattern that matched a constant), every aliased
  import (`use x as y`: `y` is renameable on its own), and every outside target
  (a host symbol, another package's definition) some reference names
  (`SymbolKind::External`, no location).
- **References:** one per resolved path *segment*: `a::b::c` references `a`,
  `b`, and `c`. Paths that end as `Res::Err` contribute none; access errors keep
  theirs; paths already resolved on input are indexed too.
- **Lookups:** `definition`, `references` (allocation-free, sorted by location),
  `resolve_at` (by HIR id), `path_references`, and `def_of` are `O(1)` or
  `O(log n)`; `at` is a binary search over the unit's name spans.
- **Rename:** `rename_set(def)` is the definition's name plus every reference
  spelling the same name (up to the case folding of a case-insensitive table:
  `GREET()` for `function Greet` is renamed too); references through an aliased import spell the alias
  and are left alone. Renaming the alias edits the alias and the references that
  went through it. Names produced by expansions are listed apart
  (`outside_source`).
- **Outline:** `document_symbols(unit)` lists item and variant definitions in
  preorder with `parent` links.

Locations come from HIR origins: a segment's origin, an item's `name_span`, a
binder's origin. A name produced by a macro or template expansion is located at
the outermost expansion's call site, with `in_source: false`. An item whose
lowering left `name_span` unset has no `location` (its `range` still locates it).

```rust
use hir_lang::{Builder, Name, Span};
use intern_lang::Interner;
use resolve_lang::SymbolKind;

// fn f(n) { n }    n bound at 5..6, used at 10..11
let mut names = Interner::new();
let n = Name::new(names.intern("n"));
let mut b = Builder::new();
b.set_span(Span::new(5, 6));
let (param, _) = b.local_param(n);
b.set_span(Span::new(10, 11));
let use_n = b.name_expr(n);
let body = b.block(&[], Some(use_n));
let f = b.func(Name::new(names.intern("f")), &[param], body);
let root = b.module(None, &[f]);
let hir = b.finish(root)?;
let unit = hir.unit();
let res = resolve_lang::resolve(hir, &names)?;
let index = res.index();

let hit = index.at(unit, 10).unwrap();             // go to definition
let def = index.definition(hit.def).unwrap();
assert_eq!(def.kind, SymbolKind::Param);
assert_eq!(def.location.unwrap().span, Span::new(5, 6));
assert_eq!(index.references(hit.def).len(), 1);     // find references
let edits = index.rename_set(hit.def).edits;        // rename
assert_eq!(edits.iter().map(|l| l.span).collect::<Vec<_>>(), [Span::new(5, 6), Span::new(10, 11)]);
assert_eq!(index.def_of(def.target), Some(hit.def));
let reference = index.references(hit.def).next().unwrap();
assert_eq!(index.resolve_at(unit, reference.path, 0), Some(hit.def));
assert_eq!(index.path_references(unit, reference.path).len(), 1);
assert_eq!(index.document_symbols(unit).len(), 1);   // outline: `f`
assert_eq!(index.references_all().len(), 1);
assert!(index.definitions().len() >= 2);
# Ok::<(), Box<dyn std::error::Error>>(())
```

### `Definition`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Definition {
    pub target: Target,
    pub name: Name,
    pub kind: SymbolKind,
    pub location: Option<Location>,   // the name; None outside the program or with no name span
    pub range: Option<Location>,      // the whole item or binder
    pub parent: Option<DefRef>,       // the enclosing item's definition
}
```

### `Reference`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reference {
    pub location: Location,
    pub def: DefRef,
    pub path: PathId,
    pub segment: u32,
    pub name: Name,            // as written
    pub via: Option<DefRef>,   // the aliased import it went through
}
```

### `References`

```rust,ignore
#[derive(Clone, Debug)]
pub struct References<'a> { /* private */ }
impl<'a> Iterator for References<'a> { type Item = &'a Reference; }
impl ExactSizeIterator for References<'_> {}
```

The references of one definition, in location order, without allocating.

### `DefRef`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefRef(/* private */);
impl DefRef { pub const fn index(self) -> usize; pub const fn from_index(i: usize) -> DefRef; }
```

A handle into [`Index::definitions`](#index). `from_index` saturates past `u32::MAX`.

### `Target`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Target { Def(DefId), Local(UnitId, BinderId), Extern(Symbol), Import(UnitId, ItemId) }
```

A definition's identity across units: an item or variant, a binder, a host
symbol, an aliased import item.

### `Location`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location { pub unit: UnitId, pub span: Span, pub in_source: bool }
```

### `Occurrence`

```rust,ignore
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Occurrence { pub def: DefRef, pub reference: Option<u32> }
impl Occurrence { pub const fn is_definition(&self) -> bool; }
```

What [`Index::at`](#index) found: the definition, and the reference (a position in
`references_all`) or `None` when the position is the definition's own name.

### `RenameSet`

```rust,ignore
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RenameSet { pub edits: Vec<Location>, pub outside_source: Vec<Location> }
```

### `SymbolKind`

```rust,ignore
#[non_exhaustive]
pub enum SymbolKind {
    Module, Function, Record, Sum, Variant, Class, Mixin, Interface, Impl, Alias, AssocType,
    Const, Global, Import, Local, Param, Capture, TypeParam, ConstParam, Region, Label, External,
}
impl SymbolKind { pub const fn name(self) -> &'static str; }
```

```rust
use hir_lang::{BinderId, Span, UnitId};
use resolve_lang::{DefRef, Location, Occurrence, RenameSet, SymbolKind, Target};

let loc = Location { unit: UnitId::new(0), span: Span::new(1, 2), in_source: true };
let set = RenameSet { edits: vec![loc], outside_source: Vec::new() };
assert_eq!(set.edits[0].span.len(), 1);
let o = Occurrence { def: DefRef::from_index(4), reference: None };
assert!(o.is_definition() && o.def.index() == 4);
assert!(matches!(Target::Local(UnitId::new(0), BinderId::from_index(0).unwrap()), Target::Local(..)));
assert_eq!(SymbolKind::External.name(), "external");
```

## Feature flags

| Feature | Default | Effect |
|---|---|---|
| `std` | yes | Enables `std` in `hir-lang` and `intern-lang`. Without it the crate needs only `alloc`. |

## Limits and complexity

- Every phase is iterative; no recursion over input. Deep nesting (100,000
  blocks, 25,000 closures, 20,000 nested classes) is tested.
- Collection, the walk, and indexing are linear in the program up to `O(log n)`
  factors (sorted tables, `lookup_local`). Lexical lookup is `O(log k)` for the
  name's key plus `O(1)` stack work.
- Glob propagation is bounded by the slots it fills (each changes a bounded
  number of times), capped by the glob budget, which also pays for choosing
  which stuck import to settle. Inheritance lookups are memoized along
  single-base chains and capped by the member budget, as is C3 linearization:
  each class with several bases costs about the total length of its bases'
  orders times their number (a "ladder" of classes each adding a base has
  orders growing linearly, so its total cost grows quadratically, as in
  Python; the budget stops it). Each did-you-mean considers at most 4,096
  candidates and is charged to the suggestion budget.
- With a case-insensitive table, one pass over the interner's symbols builds
  the fold (linear in the interned bytes; allocation only for symbols with an
  ASCII capital).
- Every arena index is a `u32`, as in hir-lang.

## What is not done yet

Stated plainly, for 0.3.0:

- **Incremental update hooks** (re-resolving one changed unit, or one changed
  item, without the rest) are v0.5.0 work.
- **symbol-lang and module-lang are not wired.** Their 1.x APIs do not fit:
  symbol-lang's table is a stack of per-scope maps without persistent scopes,
  namespaces, or name iteration (LexerSketch ISSUES M37); module-lang's graph is
  one flat namespace per module whose imports always re-export, with no aliases,
  globs, or paths (M38). resolve-lang keeps its own dense tables; wiring is
  revisited with their 2.0 APIs.
- **No `diag-lang` conversion.** Diagnostics are this crate's own type with a
  message renderer; a `diag_lang::Diagnostic` conversion is additive later.
- A glob import whose module path turns ambiguous after copying names keeps them
  (see [Imports as a fixpoint](#imports-as-a-fixpoint)).
- **PHP approximations that remain.** A value path that is not a callee finds a
  function when no constant of that name exists (PHP reports an undefined
  constant), and a callee finds a constant when no function exists (PHP fails
  at run time); both are documented leniencies, not checks. HIR paths carry no
  `$` sigil, so static properties must keep it in their names to stay apart
  from class constants. Only ASCII case folding exists (PHP 8 needs no more).
- An [`Env`](#env) is asked with names as written; a host serving a
  case-insensitive table folds them itself.
- Interface default methods do not see inherited members unqualified
  (`ClassScope` applies to classes; interface bodies are never lexical).
