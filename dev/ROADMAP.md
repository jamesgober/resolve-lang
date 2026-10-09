# resolve-lang - Roadmap

> Path from scaffold to a stable 1.0. Hard parts are front-loaded; each phase has hard exit criteria.
> Master plan: ../_lexersketch/ROADMAP.md and ../_lexersketch/NEW-LIBS.md
>
> **Anti-deferral rule:** no listed hard task moves to a later phase unless this file records the move and the reason.

## v0.1.0 - Scaffold (DONE)
Compiles, CI green, structure correct, no domain logic.
- [x] Manifest, README, CHANGELOG, REPS, dual license, CI, deny, clippy, rustfmt, DIRECTIVES, ROADMAP.

## v0.2.0 - Foundation (DONE, 2026-10-08)
- [x] Policy model (scoping, shadowing, hoisting, namespaces); resolver over HIR; diagnostics with suggestions.
- [x] Wires hir-lang (and symbol-lang/module-lang where their APIs fit). Property tests against a reference resolver.
- [x] Pulled forward from v0.5.0: imports/exports, globs, aliases, visibility; persistent index (definitions, references, rename sets).

Delivered:
- `resolve` (Tier 1), `Resolver` (Tier 2: policy, environment, budget), `Program`
  (Tier 3: several units resolved jointly, root names, packages), `Resolution`,
  `ResolvedUnit` (`members`, `ident_binds`), `ClassMember`.
- `Policy` with presets `kraken`/`php`/`python` and setters; `Namespace`, `NsSet`,
  `ItemClass`, `Hoist` (Scope, AfterDecl, Module), `Shadowing`, `Redefinition`,
  `ClassScope` (Lexical, BodyOnly, Qualified), `ModuleScope`, `RootBinding`
  (Early, Late, Unsupported), `Reexport`.
- `Env` host interface (roots, prelude, members, enumeration), `Export`,
  `DefKind`, `NoEnv`, `MapEnv`.
- Phases: collection walk; joint import resolution as a monotone least
  fixpoint (absent < one < ambiguous slots, waiters and subscriptions, final
  mode only for lexical fallbacks behind unsettled globs, recheck); the
  resolving walk (`lookup_local` + scope events + per-name shadow stacks, O(1)
  BodyOnly skipping); member tables with mixin expansion in dependency order
  and memoized inherited lookups; writes through `Hir::resolve_partial`.
- `Diagnostic`/`DiagKind` (22 kinds, messages), did-you-mean by banded edit
  distance under a cell budget.
- `Index`: definitions, per-segment references (CSR by definition and path),
  `resolve_at`, `at`, `references` (allocation-free), `rename_set`,
  `document_symbols`, expansion-aware locations.
- `Budget` (glob bindings, member steps, suggestion cells), `ResolveError`,
  `Limit`.
- Tests: unit tests per module; integration tests (lexical, imports and
  multi-unit, policies, suggestions, index, deep); differential properties
  against a reference scope-stack resolver and against a naive import fixpoint
  (plus order independence); Criterion benches at 124k and 1.24M nodes, imports,
  multi-unit, index. Examples `basic`, `multi_unit`, `lsp`.

Dependency wiring (decided here, recorded per the anti-deferral rule):
- **hir-lang 0.3: wired.** The resolver reads and writes HIR through its
  public API only: `lookup_local`, `walk_from` events, `can_reference`,
  `resolve_partial`.
- **intern-lang 1: wired.** `Lookup` spells names for suggestions and messages.
- **symbol-lang: not wired.** Its 1.x `SymbolTable` is a stack of per-scope
  maps with no persistent scope ids, no namespaces, and no name iteration
  (ISSUES M37); binders already come from hir-lang's own scope index, and
  items need namespaced, iterable, persistent tables. Revisit with symbol-lang
  2.0 (persistent scope arena).
- **module-lang: not wired.** Its 1.x `ModuleGraph` is one flat namespace per
  module whose imports always re-export, with no aliases, globs, paths, or
  ambiguity, and an O(L²) re-export check (ISSUES M38). Revisit with
  module-lang 2.0.
- **diag-lang: not wired.** Diagnostics are this crate's own `Copy` type with a
  message renderer; a `diag_lang::Diagnostic` conversion is additive.
- No `serde` feature: nothing is serialized yet.

Known gaps carried forward (see `docs/API.md#what-is-not-done-yet`):
- A glob import whose module path becomes ambiguous after copying names keeps
  them (reported); `ClassScope::Lexical` sees own members only; multiple
  inheritance is depth-first, not C3. (The last two closed in v0.3.0.)
- hir-lang gap found: `Hir::lookup_local` searches only the path's own
  namespace, so a value path's type-parameter prefix (`T::new`) is found
  through this crate's own event-driven stack instead. A
  `lookup_local_in(path, name, ns)` in hir-lang would remove that.

## v0.3.0 - Flagship semantics (DONE, 2026-10-08)
LexerSketch ISSUES P14: the PHP (Mox) and Python (Mercury) semantics needed
before the Mox Demo milestone.
- [x] Case folding per namespace table (`Case`, `Policy::with_case`); PHP 8's
  ASCII folding for functions, methods, classes, interfaces, traits, enums,
  namespaces; constants and variables case-sensitive.
- [x] PHP's separate constant table (`Namespace::Const`): a method and a class
  constant (or a function and a constant) of one name are not duplicates;
  callee-aware value lookup.
- [x] C3 method resolution order for several bases; an inconsistent hierarchy
  reported (`DiagKind::InconsistentMro`), like Python's `TypeError`.
- [x] `ClassScope::Lexical` sees inherited (and mixin) members.
- [x] The import corner (first segment missing while globs are pending):
  differential coverage generated by the reference; three bugs found and fixed.
- [x] Presets updated (`php`, `python` docs and tables); tests per item.

Delivered:
- `Case`, `Policy::with_case`/`case`, `Namespace::Const`,
  `DiagKind::InconsistentMro`; folding through every table lookup (a `Fold`
  built once from the interner, canonical per case class, so order-free);
  callee-aware tables; eager iterative C3 with a fallback order; lexical
  inherited members via set-aside outcomes finished in the member phase
  (private base members not inherited; the class header excluded); import
  settling in three tiers (exact final, forced final, cycle) instead of one;
  multi-table import resolutions in fixed table order; `rename_set` across case
  variants.
- Tests: `case_fold`, `inheritance`, `import_corner` (all differential against
  independent references), unit tests for the fold and C3. Benchmarks
  `resolve_php`, `resolve_classes`.

Dependency wiring: unchanged (hir-lang 0.3, intern-lang 1). lower-lang does not
depend on resolve-lang at run time; it publishes after this release.

Known gaps carried forward (see `docs/API.md#what-is-not-done-yet`):
- PHP leniencies: a bare function name resolves to the function when no
  constant exists, and a callee to a constant when no function exists.
- HIR paths carry no `$` sigil: static properties keep it in their names to stay
  apart from class constants (a lowering convention, documented).
- No Unicode case folding (no target language needs it).
- The hir-lang `lookup_local_in` gap (ISSUES P13) is unchanged.

## v0.5.0 - Implementation
- [ ] Incremental update hooks: re-resolve a changed unit (and the units whose imports read it) without the rest; keep the index stable across updates.
- [x] Imports/exports, globs, aliases, visibility; persistent index (definitions, references, rename sets) — delivered in v0.2.0.

## v0.9.0 - Hardening
- [ ] Fuzzing; scale benchmarks; audit with the LexerSketch LSP as consumer.

## v1.0.0 - Stable
- [ ] Frozen after the LexerSketch LSP drives go-to-definition and rename through it (D18).
