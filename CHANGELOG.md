<h1 align="center">
    <img width="90px" height="auto" src="https://raw.githubusercontent.com/jamesgober/jamesgober/main/media/icons/hexagon-3.svg" alt="Triple Hexagon">
    <br><b>CHANGELOG</b>
</h1>
<p>
  All notable changes to <code>resolve-lang</code> will be documented in this file. The format is based on <a href="https://keepachangelog.com/en/1.1.0/">Keep a Changelog</a>,
  and this project adheres to <a href="https://semver.org/spec/v2.0.0.html/">Semantic Versioning</a>.
</p>

---

## [Unreleased]

---

## [0.4.1] - 2026-10-12

Three gaps bcgen-lang 0.4 found while compiling Mox classes, closed for
`Policy::php()`: a class name in value position (the Mox sketch's `new_object`
template, `mox.new(Foo, ...)`), an interface constant reached through an
implementing class, and trait (mixin) member tables that differed from PHP.
Additive: no public item changed shape, and the new `Policy` settings are off in
every preset but `php`.

### Added

- `Policy::with_class_values` and `Policy::class_values`: a value path that
  finds nothing in the value and constant tables falls back to the type table
  and resolves to a class (or record, or a class the `Env` defines) there.
  Unqualified, module-qualified, `\`-rooted, and imported names all work, folded
  by the type table's case rule; the path ends as `Res::Def(class item)` with
  nothing left over, which is the operand shape bcgen-lang 0.4's `new`,
  `instanceof`, and `::class` read. A constant or function of the same name
  wins; a callee does not fall back (`Foo()` is not `new Foo`); an interface or
  a sum stays "expected a value" because hir-lang refuses a value path to
  one. On in `Policy::php()`, off in the other presets.
- `Policy::with_interface_members` and `Policy::interface_members`: a class
  inherits the constants and methods of the interfaces it implements (and of
  those interfaces' super-interfaces, and of its base classes' interfaces), so
  `Impl::CONST` and `self::CONST` resolve to the interface's declaration. PHP's
  order: the class and its base classes first, then the interfaces, nearest
  class first. Memoized per class and name, iterative, and charged to the
  member-step budget. On in `Policy::php()`, off elsewhere.
- Tests: `tests/php_classes.rs` (19) and `tests/php_mixins.rs` (10), including
  the bcgen-lang operand shape resolved and compared with the hand-built one,
  every value position (`new`, `instanceof`, `Foo::class`, `Foo::bar()`,
  `Foo::C`), namespaced, imported, and host-defined classes, the opt-out and
  callee cases, index and rename sets for the new references, a 50,000-deep
  interface chain, a 20,000-deep class chain, a class implementing 600
  interfaces under a small budget, two mixins of 30,000 methods with 60,000 rules, looping hierarchies, and three properties:
  `Ni::Kn` against a reference of PHP's lookup order on random class and
  interface hierarchies, class-name spellings in random case, and every member
  of every class against a model of PHP's trait copying on random mixin graphs.
  Unit tests for the new settings and the class-like kinds; example
  `php_classes`; benchmark `resolve_php_classes` (10,000 classes, 245k nodes,
  about 180-220 ms on a loaded machine; about 160 ms with both settings off).
  The existing benchmarks do not move beyond their noise.

### Fixed

- **Mixin member tables followed PHP only partly** (found by bcgen-lang's
  `tests/mixins.rs`, which counted 16 differing members in 200 random
  programs; the same model now agrees on 20,000 and on `tests/php_mixins.rs`'s
  1,500 cases):
  - A visibility-only `as` rule on a method an `insteadof` rule had excluded
    brought the excluded method back. PHP applies the rule to the copy, and
    there is none.
  - An `as` alias replaced a member of the same name that an earlier mixin
    gave; PHP keeps the first (and reports the collision). Aliases are now
    added before their method, mixin by mixin in `use` order, and the first
    member of a name wins.
  - `insteadof` and `as` rules matched a mixin's constants, properties, and
    static properties as well as its methods; they name methods only (a rule
    that names nothing else is `UnknownMixinMember`, as before).
  - An abstract mixin method could stand in for, or hide, a concrete one; an
    abstract method now never replaces a member, and a concrete one replaces
    an abstract one an earlier mixin brought.
  - The same function reaching a class twice at different visibilities (a
    mixin used through two others with a visibility rule on one path) was not a
    conflict; it is `MixinConflict` now, as PHP's collision check has it. The
    same function at the same visibility (a diamond) stays no conflict.

### Changed

- Under `Policy::php()` (behavior, not API): programs that used to get
  "expected a value, found class `Foo`" for `new Foo` now resolve; `Impl::X`
  for an interface constant used to stay type-directed (`Res::Def(Impl)`,
  one segment left) and now resolves to the constant; and a program that
  relied on one of the mixin table bugs above gets the PHP table and, in the
  conflict cases, a `MixinConflict`. Every other preset resolves as before.
  A caller that wants exactly the 0.4.0 resolution under `Policy::php()` can
  turn the two new settings off (the mixin fixes have no switch).

---

## [0.4.0] - 2026-10-11

Moves resolve-lang to hir-lang 0.4 (HIR spec v3), so it shares one `hir_lang`
with typeck-lang 0.3 and the rest of the LexerSketch chain, and resolves every
form 0.4 added: place-once aliases (`let_place`), keyed `yield` and
`yield from`, and union and intersection types.

### Breaking

- **Depends on `hir-lang` 0.4** (was 0.3). The `Hir` that `resolve`,
  `Resolver::resolve`, and `Program::add_unit` take, and the one
  `Resolution::hir` returns, is hir-lang 0.4's; a caller still on hir-lang 0.3
  gets two incompatible `hir_lang` crates (rustc E0308).
- `SymbolKind` has a new variant, `Place` (the enum is `#[non_exhaustive]`, so
  only code that relied on the variant list changes).

### Added

- Resolution of the HIR 0.4 forms. `Expr::LetPlace`: the place's operands
  resolve in the enclosing scope, the alias (`BinderKind::Place`) in the body
  only; named from a closure in the body it is `CannotCapture` (a place alias
  crosses no frame); a template's alias carries its expansion's mark, so user
  names in the body never resolve to it and are never offered it as a
  suggestion. `Expr::Yield { key, value }` (key, then value) and
  `Expr::YieldFrom`. Every type path inside `Ty::Union` and
  `Ty::Intersection` members resolves like any type path.
- `SymbolKind::Place` (`"place alias"`) for `let_place` aliases in the index.
- Tests: `tests/hir_0_4.rs` (19): `let_place` scoping, nested aliases, an item
  in the body, closures, shadowing policies, template hygiene and suggestions,
  index and rename sets for template and source aliases; keyed yields and
  `yield from`; union and intersection members, wrong-kind and unknown
  members, a repeated member normalization drops, nested and nullable members;
  the HIR spec §9.6 example (Mox `.=` with a union parameter) resolved under
  `Policy::php()` and printed exactly as the spec prints it; HIR repaired by
  `finish_lenient`; two cases that back the `lookup_local_in` decision. The
  differential property tests (`tests/properties.rs`) now generate generic
  parameters, `let_place`, keyed `yield` and `yield from`, and union,
  intersection, and nullable annotations, with the reference resolver extended
  to match; the two recorded shrunk failures of 0.2 are kept as an explicit
  test. Benchmark `resolve_hir_0_4_forms` (192,000 nodes of place aliases,
  keyed yields, and union-typed parameters).

### Changed

- `Shadowing::DenySameScope` and `Shadowing::DenyLocals` exempt place
  aliases: lowering introduces them, the user never declares them, so an alias
  is not reported and a local declared inside its body is not reported for
  reusing its name.
- hir-lang 0.4's behaviour changes reach resolution as follows, each covered
  by a test: unions come back normalized from `finish` (sorted, flattened,
  repeats dropped), and the dropped members are dead error paths that the
  resolver neither resolves, diagnoses, nor indexes; the same holds for
  subtrees a lenient repair cut off. The new unreachable reporting and the
  two-round lenient repair change what hir-lang reports, not what reaches the
  resolver; resolve-lang's existing tests passed against hir-lang 0.4
  before any of them was extended.
- `Hir::lookup_local_in` (hir-lang 0.4, LexerSketch ISSUES P13) is not used:
  the type table's shadow stack already finds a type parameter from a path in
  another namespace, and it also folds case in a case-insensitive type table
  and meets value paths in a merged table, which an exact-name lookup in one
  namespace does not.

### Migration

Bump both crates together:

```toml
[dependencies]
resolve-lang = "0.4"
hir-lang = "0.4"
```

and follow hir-lang's own 0.4 migration for the HIR you build (`Yield { key,
value }`, `BinderKind::Place`, `OpKind::BitNot`). Nothing in resolve-lang's own
API changed shape except the new `SymbolKind::Place`.

---

## [0.3.0] - 2026-10-08

The flagship semantics: what PHP (Mox) and Python (Mercury) need from name
resolution before the Mox Demo milestone (LexerSketch ISSUES P14). Names fold
case per table as PHP 8 does; PHP's constants live apart from its functions and
methods; several bases follow Python's C3 method resolution order; unqualified
names inside a class see inherited members; and the import corner (a relative
import whose first segment is missing while globs are still pending) is held to
a differential test, which found and fixed three ordering bugs.

### Breaking

- `Namespace` has a sixth variant, `Const`, and `Namespace::ALL` has six
  entries. Constants (`ItemClass::Const`) occupy `Const`, which every preset
  except `php` merges into `Value`, so other policies resolve as before.
- `Policy::php()` now keeps constants, globals, and static properties in their
  own case-sensitive table; folds function, method, class, interface, trait,
  enum, and namespace names (ASCII, as PHP 8); and makes records, sums,
  classes, and interfaces types only (a PHP function and class may share a
  name). Programs that relied on a PHP class name being a value, on a method
  and a class constant of one name being reported as duplicates, or on case
  mattering for functions resolve differently.
- Several bases are searched in C3 method resolution order instead of
  depth-first, left to right; an inconsistent hierarchy is reported as the new
  `DiagKind::InconsistentMro`.
- Under `ClassScope::Lexical` (the default and `kraken` policies), an
  unqualified name inside a class body now finds inherited members (and mixin
  members) before enclosing scopes.
- `ClassMember::name` is the name as written (an alias's new name), and members
  are sorted by namespace, then by table key.
- An import that binds several tables resolves its path to the first table (in
  the order value, type, module, macro, constant) holding one meaning, no
  longer to whichever table filled first.

### Added

- `Case` (`Sensitive`, `AsciiInsensitive`; `#[non_exhaustive]`),
  `Policy::with_case`, and `Policy::case`: case folding per table, applied to
  every lookup (unqualified names, module paths, imports, class members, mixin
  rules, unit roots, duplicate detection). Names stay as written in
  diagnostics, members, and the index; `Index::rename_set` includes references
  spelled in another case (not ones through an aliased import).
- `Namespace::Const` and callee-aware value lookup: a call's callee searches
  functions first, any other value path constants first.
- C3 linearization of every class with several bases, eagerly and without
  recursion, charged to the member budget; `DiagKind::InconsistentMro { class }`
  with the fallback order (bases' orders concatenated without repeats).
- Inherited members in lexical class scopes, resolved after member tables
  exist: the first member in method resolution order the class may use (a
  base's private member is not inherited); locals and own members still win;
  the class header (bases, interfaces, mixin uses) never sees them.
- Tests: `tests/case_fold.rs` (PHP tables against a reference of plain maps on
  random programs; folding invisible on lowercase programs; worked cases),
  `tests/inheritance.rs` (C3 and lexical inheritance against a textbook C3
  reference on random hierarchies with public, protected, and private members,
  under the Kraken and Python policies), `tests/import_corner.rs` (relative
  imports whose first segment arrives only through globs, or falls back to the
  enclosing module, against a naive fixpoint over per-table slots, under
  isolated and lexical module scoping); unit tests for the fold, C3 (the
  textbook example, a diamond, inconsistent and repeated bases, cycles, the
  budget). Benchmarks `resolve_php` (124k nodes, every call found through
  folding) and `resolve_classes` (10,000 classes with three bases each).

### Fixed

- Final-mode import settling no longer fails an import as an `ImportCycle`
  while the import it waits on could still be settled through a fallback:
  glob-blocked waits are settled before import-blocked ones, and a final-mode
  attempt keeps waiting on names a pending named import binds.
- Final mode no longer treats every glob-pending miss on an import's path as
  absent: an *exact* final mode relaxes only names no pending import could
  still produce, and is preferred; the old *forced* mode runs only when no
  exact choice exists.
- An import that binds several tables no longer keeps the resolution of the
  table that happened to fill first after an earlier table fills or turns
  ambiguous; the result no longer depends on settling order.
- A PHP method and class constant of one name are no longer reported as
  duplicates.

---

## [0.2.0] - 2026-10-08

The foundation: name resolution over HIR. Every path and bare-identifier
pattern of a `hir-lang` program is bound under a language's scoping policy,
across units and imports, with diagnostics and did-you-mean suggestions, and a
persistent definition/reference index for editor tooling.

### Added

- `resolve`: the lazy path, one unit under the default (lexical) policy.
- `Policy`, a language's scoping rules as data: hoisting per item class
  (`Hoist::Scope`, `AfterDecl`, `Module`), which namespaces each item class
  occupies and which namespaces share a table (`Namespace`, `NsSet`, merging),
  shadowing (`Shadowing`), redefinition (`Redefinition`), what a class body
  shows its methods (`ClassScope::Lexical`, `BodyOnly`, `Qualified`), nested
  modules (`ModuleScope`), early or late binding of `self::`/`parent::`/
  `static::` (`RootBinding`), visibility enforcement and descendant access,
  import forms and re-export (`Reexport`), implicit globals. Presets
  `kraken`, `php`, `python`.
- `Resolver` (one unit with a policy, an environment, and a budget) and
  `Program` (several units resolved against each other, with root names and
  packages).
- `Env`, the host interface for names outside the program (roots, prelude,
  members of outside containers, enumeration for globs and suggestions), with
  `Export`, `DefKind`, `NoEnv`, and the in-memory `MapEnv`.
- Lexical resolution through `Hir::lookup_local` and the walk's scope events,
  with per-name shadow stacks for items and imports: innermost wins by scope
  depth and position; locals behind a frame are reported, not skipped.
- Paths through modules, sum variants, classes, and outside containers, with
  partial (type-directed) resolution for the rest; `::`, `self::`, `super::`
  roots; qualified selves; access checks with private-to-descendants.
- Imports resolved jointly as a monotone least fixpoint over all units:
  single, aliased, glob, public/private re-export, cycles across modules and
  units, glob ambiguity reported at the use site, import cycles, broken
  imports; an import never resolves through itself.
- Bare identifier patterns (`Pat::Ident`) match constants, unit variants, and
  unit records, and bind otherwise.
- Class member tables with mixin expansion (`insteadof`, `as` with rename and
  visibility, mixins of mixins in dependency order), inherited lookups
  memoized along single-base chains, private/protected member access.
- `Diagnostic` and `DiagKind` (`#[non_exhaustive]`, 22 kinds) with English
  messages and did-you-mean suggestions from a banded edit distance over the
  visible names, charged to a budget.
- `Index`: definitions (items, variants, binders, aliased imports, outside
  targets), references per path segment (CSR by definition and by path),
  go-to-definition by HIR id and by source offset, find-references (an
  allocation-free iterator), rename sets that include import paths and skip
  uses through aliases, document symbols, origins mapped through expansions to
  source spans.
- `Budget` (glob bindings, member steps, suggestion cells), `ResolveError`
  (`#[non_exhaustive]`), `Limit`.
- `ResolvedUnit::members` (effective class members after mixins) and
  `ResolvedUnit::ident_binds`.
- Tests: unit tests per module; integration tests for lexical scoping,
  imports and multi-unit programs, PHP/Python/Kraken policies, suggestions,
  the index, and hostile depths; differential property tests against a
  reference scope-stack resolver and against a naive import fixpoint (with an
  order-independence property); Criterion benchmarks at 124k and 1.24M nodes,
  an import-heavy program, a multi-unit program, and index queries. Examples
  `basic`, `multi_unit`, `lsp`.

### Changed

- Wired `hir-lang` 0.3 and `intern-lang` 1. `symbol-lang` and `module-lang`
  are deliberately not wired (their 1.x APIs do not fit; `dev/ROADMAP.md`
  records why).
- Pulled imports, globs, aliases, visibility, and the persistent index
  (planned for 0.5.0) into 0.2.0; incremental update hooks remain 0.5.0.

---

## [0.1.0] - 2026-10-08

Initial scaffold and repository bootstrap. No domain logic yet &mdash; this release establishes the structure, tooling, and quality gates the implementation will be built on.

### Added

- `Cargo.toml` with crate metadata, Rust 2024 edition, MSRV 1.85.
- Dual `Apache-2.0 OR MIT` license files.
- `README.md`, `CHANGELOG.md`, and a documentation skeleton.
- `REPS.md` compliance baseline.
- `.github/workflows/ci.yml` CI matrix; `deny.toml`, `clippy.toml`, `rustfmt.toml`.
- `dev/DIRECTIVES.md` and `dev/ROADMAP.md` (committed engineering standards + plan).

[Unreleased]: https://github.com/jamesgober/resolve-lang/compare/v0.4.1...HEAD
[0.4.1]: https://github.com/jamesgober/resolve-lang/compare/v0.4.0...v0.4.1
[0.4.0]: https://github.com/jamesgober/resolve-lang/compare/v0.3.0...v0.4.0
[0.3.0]: https://github.com/jamesgober/resolve-lang/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/jamesgober/resolve-lang/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/jamesgober/resolve-lang/releases/tag/v0.1.0
