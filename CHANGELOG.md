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

[Unreleased]: https://github.com/jamesgober/resolve-lang/compare/v0.3.0...HEAD
[0.3.0]: https://github.com/jamesgober/resolve-lang/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/jamesgober/resolve-lang/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/jamesgober/resolve-lang/releases/tag/v0.1.0
