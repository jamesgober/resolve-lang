<h1 align="center">
    <img width="99" alt="Rust logo" src="https://raw.githubusercontent.com/jamesgober/rust-collection/72baabd71f00e14aa9184efcb16fa3deddda3a0a/assets/rust-logo.svg">
    <br>
    <b>resolve-lang</b>
    <br>
    <sub><sup>HIR NAME RESOLUTION</sup></sub>
</h1>

<div align="center">
    <a href="https://crates.io/crates/resolve-lang"><img alt="Crates.io" src="https://img.shields.io/crates/v/resolve-lang"></a>
    <a href="https://crates.io/crates/resolve-lang"><img alt="Downloads" src="https://img.shields.io/crates/d/resolve-lang?color=%230099ff"></a>
    <a href="https://docs.rs/resolve-lang"><img alt="docs.rs" src="https://img.shields.io/docsrs/resolve-lang"></a>
    <a href="https://github.com/jamesgober/resolve-lang/actions"><img alt="CI" src="https://github.com/jamesgober/resolve-lang/actions/workflows/ci.yml/badge.svg"></a>
    <a href="https://github.com/rust-lang/rfcs/blob/master/text/2495-min-rust-version.md"><img alt="MSRV" src="https://img.shields.io/badge/MSRV-1.85%2B-blue"></a>
</div>

<br>

<div align="left">
    <p>
        <strong>resolve-lang</strong> binds every name in a <a href="https://crates.io/crates/hir-lang"><code>hir-lang</code></a> program to what it names: locals, items, imports, members, the host's built-ins. One resolver serves every language the <code>-lang</code> family forges, because each language reaches it as HIR and its scoping rules are a <strong>policy</strong> &mdash; when items become visible, which namespaces share a table, what a method sees of its class, how <code>self::</code>, <code>parent::</code>, and <code>static::</code> bind, how imports re-export &mdash; rather than a separate resolver.
    </p>
    <p>
        Names that do not resolve become diagnostics with did-you-mean suggestions; the resolved program comes back as a valid <code>Hir</code>, written through hir-lang's checked setters; and a persistent <strong>index</strong> of definitions and references answers what an editor asks: go to definition, find references, the edits of a rename, the document outline. Several units resolve together, imports in cycles included.
    </p>
    <br>
    <hr>
    <p>
        <strong>MSRV is 1.85+</strong> (Rust 2024 edition). <code>no_std</code>-compatible (needs only <code>alloc</code>), <code>#![forbid(unsafe_code)]</code>, two dependencies from the family: <a href="https://crates.io/crates/hir-lang"><code>hir-lang</code></a> and <a href="https://crates.io/crates/intern-lang"><code>intern-lang</code></a>.
    </p>
    <blockquote>
        <strong>Status: 0.2.0, pre-1.0.</strong> The public API is designed across the 0.x series and frozen at <code>1.0.0</code>, after the LexerSketch LSP drives go-to-definition and rename through it. See <a href="./CHANGELOG.md"><code>CHANGELOG.md</code></a> and <a href="./dev/ROADMAP.md"><code>dev/ROADMAP.md</code></a>.
    </blockquote>
</div>

<hr>
<br>

## The model

- **[`resolve`](./docs/API.md#resolve)** resolves one unit with the default (lexical, Kraken-style) policy: the lazy path.
- A **[`Policy`](./docs/API.md#policy)** is a language's scoping rules as data. Presets: [`kraken`](./docs/API.md#policykraken), [`php`](./docs/API.md#policyphp), [`python`](./docs/API.md#policypython).
- A **[`Resolver`](./docs/API.md#resolver)** resolves one unit with a policy, an [`Env`](./docs/API.md#env) (names outside the program: other packages, the standard library, primitive types), and a [`Budget`](./docs/API.md#budget).
- A **[`Program`](./docs/API.md#program)** resolves several units against each other; a unit given a root name is reachable from every unit as `name::item`.
- The **[`Resolution`](./docs/API.md#resolution)** holds the resolved units, the **[`Diagnostic`](./docs/API.md#diagnostic)**s, and the **[`Index`](./docs/API.md#index)**.

<br>

What it guarantees, and how each guarantee is checked:

| Guarantee | How it is held |
|---|---|
| Lexical resolution is right: the innermost visible binder or item wins, hoisting and frames included. | Property tests compare it with a separate reference resolver (a stack of scopes searched innermost-out) on random programs of nested blocks, items, closures, and parameters, under scope hoisting and under declare-before-use. |
| Imports reach the least fixpoint of their rules, whatever the order. | Property tests compare it with a naive fixpoint over random module graphs of definitions, aliased imports, and globs, public and private, with cycles and ambiguity; a second property permutes the modules and checks that nothing changes. |
| Every reference ends resolved, or with exactly one diagnostic. | Checked by the property tests on every random program; access errors keep their resolution and carry one diagnostic. |
| The result is a valid `Hir`. | Every resolution goes through `Hir::resolve_partial`; a refusal becomes `Res::Err` and a diagnostic. The tests validate the result again. |
| The index is consistent: a definition lists exactly the references that point at it. | Checked by the property tests on every random program. |
| No recursion over input; deep or wide programs never overflow the stack. | Tests resolve 100,000 nested blocks, 25,000 nested closures, 20,000 classes nested through method bodies, and a 50,000-item module. |
| Untrusted input cannot drive unbounded work. | Glob propagation, inheritance walks, and did-you-mean comparisons each run against an explicit [`Budget`](./docs/API.md#budget); exceeding the first two fails the run cleanly, the third only stops suggesting. |

<hr>
<br>

## Installation

```toml
[dependencies]
resolve-lang = "0.2"
hir-lang = "0.3"
intern-lang = "1"
```

Without the standard library:

```toml
[dependencies]
resolve-lang = { version = "0.2", default-features = false }
```

<hr>
<br>

## Quick start

Build a unit with hir-lang's builder, resolve it, read the result:

```rust
use hir_lang::{Builder, Expr, Name, Res};
use intern_lang::Interner;

// fn length(n) { n }      fn main() { lenght }
let mut names = Interner::new();
let n = Name::new(names.intern("n"));
let mut b = Builder::new();
let (param, n_binder) = b.local_param(n);
let use_n = b.name_expr(n);
let body = b.block(&[], Some(use_n));
let length = b.func(Name::new(names.intern("length")), &[param], body);
let typo = b.name_expr(Name::new(names.intern("lenght")));
let main_body = b.block(&[], Some(typo));
let main = b.func(Name::new(names.intern("main")), &[], main_body);
let root = b.module(None, &[length, main]);
let hir = b.finish(root)?;
let unit = hir.unit();

let res = resolve_lang::resolve(hir, &names)?;
let hir = res.hir(unit).unwrap();
let Expr::Path(p) = *hir.expr(use_n) else { unreachable!() };
assert_eq!(hir.path(p).res, Res::Local(n_binder));
assert_eq!(
    res.diagnostics()[0].message(&names),
    "cannot find value `lenght` in this scope; did you mean `length`?",
);
# Ok::<(), Box<dyn std::error::Error>>(())
```

### A language's policy and environment

```rust
use hir_lang::{Builder, Name, Ns, Prim, Res, Ty};
use intern_lang::Interner;
use resolve_lang::{DefKind, Export, MapEnv, Namespace, Policy, Resolver};

let mut names = Interner::new();
let int = Name::new(names.intern("int"));
// The host provides primitive type names.
let env = MapEnv::new().with_prelude(int, Namespace::Type, Export::new(Res::Prim(Prim::I64), DefKind::Prim));

// type Count = int
let mut b = Builder::new();
let path = b.name_path(int, Ns::Type);
let ty = b.ty(Ty::Path(path));
let alias = b.item(hir_lang::Item::new(
    Some(Name::new(names.intern("Count"))),
    hir_lang::ItemKind::Alias { generics: hir_lang::Generics::default(), ty },
));
let root = b.module(None, &[alias]);

let res = Resolver::new(Policy::python()).with_env(&env).resolve(b.finish(root)?, &names)?;
assert_eq!(res.units()[0].hir().path(path).res, Res::Prim(Prim::I64));
# Ok::<(), Box<dyn std::error::Error>>(())
```

### Several units, and the index

```rust
use hir_lang::{Builder, FnDef, Item, ItemKind, Name, Ns, Path, Segment, UnitId, Vis};
use intern_lang::Interner;
use resolve_lang::{Policy, Program, Target};

let mut names = Interner::new();
let (util, helper) = (Name::new(names.intern("util")), Name::new(names.intern("helper")));

// Unit 1, reachable as `util`: pub fn helper() {}
let mut b = Builder::for_unit(UnitId::new(1));
let body = b.block(&[], None);
let f = b.item(Item::new(Some(helper), ItemKind::Fn(FnDef { body: Some(body), ..FnDef::default() })).with_vis(Vis::Public));
let root = b.module(None, &[f]);
let util_hir = b.finish(root)?;

// Unit 2: fn main() { util::helper }
let mut b = Builder::for_unit(UnitId::new(2));
let segs = [Segment::new(util, b.origin()), Segment::new(helper, b.origin())];
let segs = b.list(&segs);
let path = b.path(Path::new(segs, Ns::Value));
let call = b.expr(hir_lang::Expr::Path(path));
let body = b.block(&[], Some(call));
let main = b.func(Name::new(names.intern("main")), &[], body);
let root = b.module(None, &[main]);
let app_hir = b.finish(root)?;

let mut program = Program::new(Policy::kraken());
program.add_unit(Some(util), util_hir);
program.add_unit(None, app_hir);
let res = program.resolve(&names)?;
assert!(res.is_clean());

// Find references: `util::helper` is one reference to `helper`.
let index = res.index();
let def = index.def_of(Target::Def(hir_lang::DefId::foreign(UnitId::new(1), hir_lang::Def::Item(f)))).unwrap();
assert_eq!(index.references(def).len(), 1);
assert_eq!(index.resolve_at(UnitId::new(2), path, 1), Some(def));
# Ok::<(), Box<dyn std::error::Error>>(())
```

More in [`examples/`](./examples): `basic` (the lazy path), `multi_unit` (two units importing each other), `lsp` (go-to-definition, references, rename, outline).

<hr>
<br>

## What resolution covers

- **Binders** through `Hir::lookup_local` and the walk's `Bind`/`Scope`/`Frame` events: the HIR's own scope rules, never re-derived. A local behind a frame it cannot cross (a nested function) is reported, not silently skipped.
- **Items** by namespace and hoisting: visible in their whole scope, from their declaration on, or (PHP) in their whole module wherever declared.
- **Paths**: `a::b::c` through modules, sum variants, and the environment's containers; partial resolution where the rest is type-directed (`Vec::new`, `T::Item`, `<T as Tr>::Out`); roots `::`, `self::`, `super::`; `self::`/`parent::`/`static::` early or late per policy.
- **Imports**: single, aliased, glob, re-exported, private, across units, in cycles; ambiguity between globs reported where the name is used.
- **Patterns**: a bare identifier pattern matches a constant, unit variant, or unit record of that name, and binds otherwise.
- **Classes**: member tables with mixin expansion (`insteadof`, `as`), inherited lookups, private and protected access.
- **Diagnostics**: unresolved names (with a suggestion within a small edit distance), ambiguous globs, private access, duplicates, uncapturable locals, wrong kinds, import cycles, mixin conflicts.

<hr>
<br>

## Performance

Measured with `cargo bench --bench bench` on a desktop x86_64 machine (Windows, release profile), resolution only (building the HIR is excluded):

| Benchmark | Size | Time |
|---|---|---|
| One unit, functions with locals and calls | 124,000 nodes | 24.6 ms |
| One unit, functions with locals and calls | 1,240,000 nodes | 317 ms |
| 1,000 modules in a glob ring, aliased imports | 53,000 nodes | 19.9 ms |
| Eight units, each calling into the next | 992,000 nodes | 263 ms |

These are library numbers: the time includes building the index and writing every resolution into the `Hir`.

<hr>
<br>

## Testing

```sh
cargo test --all-features
cargo clippy --all-targets --all-features -- -D warnings
cargo bench --bench bench
```

The property tests in [`tests/properties.rs`](./tests/properties.rs) and [`tests/import_graph.rs`](./tests/import_graph.rs) hold the resolver to independent references written in the tests. Every `rust` example in this README and in [`docs/API.md`](./docs/API.md) is compiled and run as a doctest.

<hr>
<br>

## Cross-platform support

- Linux (x86_64, aarch64)
- macOS (x86_64, Apple Silicon)
- Windows (x86_64)

The crate uses no operating-system facilities and no platform-specific code.

<hr>
<br>

## Contributing

See [`REPS.md`](./REPS.md) for the engineering standards every change is held to, [`dev/DIRECTIVES.md`](./dev/DIRECTIVES.md) for the definition of done, and [`dev/ROADMAP.md`](./dev/ROADMAP.md) for the plan. Before a PR: `cargo fmt --all`, `cargo clippy --all-targets --all-features -- -D warnings`, and `cargo test --all-features` must be clean.

<br>

<div id="license">
    <h2>License</h2>
    <p>Licensed under either of</p>
    <ul>
        <li><b>Apache License, Version 2.0</b> &mdash; <a href="./LICENSE-APACHE">LICENSE-APACHE</a></li>
        <li><b>MIT License</b> &mdash; <a href="./LICENSE-MIT">LICENSE-MIT</a></li>
    </ul>
    <p>at your option.</p>
</div>

<div align="center">
  <h2></h2>
  <sup>COPYRIGHT <small>&copy;</small> 2026 <strong>James Gober.</strong></sup>
</div>
