# resolve-lang - Roadmap

> Path from scaffold to a stable 1.0. Hard parts are front-loaded; each phase has hard exit criteria.
> Master plan: ../_lexersketch/ROADMAP.md and ../_lexersketch/NEW-LIBS.md
>
> **Anti-deferral rule:** no listed hard task moves to a later phase unless this file records the move and the reason.

## v0.1.0 - Scaffold (DONE)
Compiles, CI green, structure correct, no domain logic.
- [x] Manifest, README, CHANGELOG, REPS, dual license, CI, deny, clippy, rustfmt, DIRECTIVES, ROADMAP.

## v0.2.0 - Foundation
- [ ] Policy model (scoping, shadowing, hoisting, namespaces); resolver over HIR; diagnostics with suggestions.
- [ ] Wires hir-lang (and symbol-lang/module-lang where their APIs fit). Property tests against a reference resolver.

## v0.5.0 - Implementation
- [ ] Imports/exports, globs, aliases, visibility; persistent index (definitions, references, rename sets); incremental update hooks.

## v0.9.0 - Hardening
- [ ] Fuzzing; scale benchmarks; audit with the LexerSketch LSP as consumer.

## v1.0.0 - Stable
- [ ] Frozen after the LexerSketch LSP drives go-to-definition and rename through it (D18).
