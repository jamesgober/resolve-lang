//! Criterion benchmarks at realistic scale: whole-unit resolution at about
//! 100k and 1M HIR nodes, an import-heavy multi-module program, a
//! multi-unit program, and index queries.

#![allow(clippy::unwrap_used, clippy::expect_used, missing_docs)]

use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use hir_lang::{
    Binder, BinderKind, Builder, Expr, ExprId, FnDef, Hir, IdKind, Item, ItemId, ItemKind, Name,
    Ns, Param, Path, PathRoot, Segment, Span, UnitId, Vis,
};
use intern_lang::Interner;
use resolve_lang::{Policy, Program, Resolver};

/// A unit of `fns` functions, each with two parameters, six `let`s chaining
/// on each other and on the parameters, and calls of other functions; the
/// first one calls into `other` (another unit's root name) when given.
fn lexical_program(unit: u32, fns: usize, other: Option<Name>, names: &mut Interner) -> Hir {
    let mut b = Builder::for_unit(UnitId::new(unit));
    let mut pos = 0u32;
    let fn_names: Vec<Name> = (0..fns)
        .map(|i| Name::new(names.intern(&format!("f{i}"))))
        .collect();
    let locals: Vec<Name> = (0..8)
        .map(|i| Name::new(names.intern(&format!("v{i}"))))
        .collect();
    let mut items: Vec<ItemId> = Vec::with_capacity(fns);
    let use_name = |b: &mut Builder, parts: &[Name], pos: &mut u32| -> ExprId {
        *pos += 2;
        b.set_span(Span::new(*pos, *pos + 1));
        let segs: Vec<Segment> = parts.iter().map(|n| Segment::new(*n, b.origin())).collect();
        let segs = b.list(&segs);
        let p = b.path(Path::new(segs, Ns::Value));
        b.expr(Expr::Path(p))
    };
    for (i, &fname) in fn_names.iter().enumerate() {
        let params: Vec<hir_lang::ParamId> = (0..2)
            .map(|j| {
                let binder = b.binder(Binder::new(locals[j], BinderKind::Param));
                let pat = b.bind(binder);
                b.param(Param::new(pat))
            })
            .collect();
        let mut stmts = Vec::new();
        for j in 2..8 {
            let x = use_name(&mut b, &[locals[j - 1]], &mut pos);
            let y = use_name(&mut b, &[locals[j - 2]], &mut pos);
            let target = fn_names[(i * 31 + j) % fns];
            let callee = match other {
                Some(o) if j == 2 => use_name(&mut b, &[o, target], &mut pos),
                _ => use_name(&mut b, &[target], &mut pos),
            };
            let call = b.call(callee, &[x, y]);
            let binder = b.binder(Binder::new(locals[j], BinderKind::Local));
            let pat = b.bind(binder);
            stmts.push(b.let_stmt(pat, Some(call)));
        }
        let tail = use_name(&mut b, &[locals[7]], &mut pos);
        let body = b.block(&stmts, Some(tail));
        let params = b.list(&params);
        items.push(
            b.item(
                Item::new(
                    Some(fname),
                    ItemKind::Fn(FnDef {
                        params,
                        body: Some(body),
                        ..FnDef::default()
                    }),
                )
                .with_vis(Vis::Public),
            ),
        );
    }
    let root = b.module(None, &items);
    b.finish(root).unwrap()
}

fn nodes(hir: &Hir) -> u64 {
    [
        IdKind::Item,
        IdKind::Expr,
        IdKind::Stmt,
        IdKind::Pat,
        IdKind::Ty,
        IdKind::Path,
        IdKind::Param,
    ]
    .iter()
    .map(|k| hir.count(*k) as u64)
    .sum()
}

fn bench_lexical(c: &mut Criterion) {
    let mut group = c.benchmark_group("resolve_unit");
    group.sample_size(10);
    for fns in [2_000usize, 20_000] {
        let mut names = Interner::new();
        let hir = lexical_program(0, fns, None, &mut names);
        let n = nodes(&hir);
        group.throughput(Throughput::Elements(n));
        group.bench_with_input(BenchmarkId::new("nodes", n), &hir, |bench, hir| {
            bench.iter_batched(
                || hir.clone(),
                |h| resolve_lang::resolve(h, &names).unwrap(),
                BatchSize::LargeInput,
            );
        });
    }
    group.finish();
}

/// `modules` modules, each defining up to `per` public functions,
/// glob-importing the next module and importing one name of the one after
/// by alias, plus a probe function using every module's names through paths.
fn import_program(modules: usize, per: usize, names: &mut Interner) -> Hir {
    let mut b = Builder::new();
    let mod_names: Vec<Name> = (0..modules)
        .map(|i| Name::new(names.intern(&format!("m{i}"))))
        .collect();
    let item_names: Vec<Name> = (0..per)
        .map(|i| Name::new(names.intern(&format!("g{i}"))))
        .collect();
    let alias = Name::new(names.intern("alias"));
    let mut mods = Vec::new();
    for m in 0..modules {
        let mut items = Vec::new();
        for (j, &n) in item_names.iter().enumerate() {
            if (j + m) % 3 == 0 {
                continue;
            }
            let body = b.block(&[], None);
            items.push(
                b.item(
                    Item::new(
                        Some(n),
                        ItemKind::Fn(FnDef {
                            body: Some(body),
                            ..FnDef::default()
                        }),
                    )
                    .with_vis(Vis::Public),
                ),
            );
        }
        let next = mod_names[(m + 1) % modules];
        let seg = Segment::new(next, b.origin());
        let segs = b.list(&[seg]);
        let path = b.path(Path {
            root: PathRoot::Super(1),
            ..Path::new(segs, Ns::Import)
        });
        items.push(
            b.item(Item::new(None, ItemKind::Import { path, glob: true }).with_vis(Vis::Public)),
        );
        let after = mod_names[(m + 2) % modules];
        let segs = [
            Segment::new(after, b.origin()),
            Segment::new(item_names[1], b.origin()),
        ];
        let segs = b.list(&segs);
        let path = b.path(Path {
            root: PathRoot::Super(1),
            ..Path::new(segs, Ns::Import)
        });
        items.push(b.item(Item::new(
            Some(alias),
            ItemKind::Import { path, glob: false },
        )));
        mods.push(b.module(Some(mod_names[m]), &items));
    }
    let mut uses = Vec::new();
    for &m in &mod_names {
        for &n in item_names.iter().take(4) {
            let segs = [Segment::new(m, b.origin()), Segment::new(n, b.origin())];
            let segs = b.list(&segs);
            let p = b.path(Path::new(segs, Ns::Value));
            uses.push(b.expr(Expr::Path(p)));
        }
    }
    let list = b.list(&uses);
    let t = b.expr(Expr::Tuple(list));
    let body = b.block(&[], Some(t));
    mods.push(b.func(Name::new(names.intern("main")), &[], body));
    let root = b.module(None, &mods);
    b.finish(root).unwrap()
}

fn bench_imports(c: &mut Criterion) {
    let mut group = c.benchmark_group("resolve_imports");
    group.sample_size(10);
    let mut names = Interner::new();
    let hir = import_program(1_000, 30, &mut names);
    let n = nodes(&hir);
    group.throughput(Throughput::Elements(n));
    group.bench_function(BenchmarkId::new("glob_ring_1000_modules", n), |bench| {
        bench.iter_batched(
            || hir.clone(),
            |h| Resolver::new(Policy::new()).resolve(h, &names).unwrap(),
            BatchSize::LargeInput,
        );
    });
    group.finish();
}

fn bench_program(c: &mut Criterion) {
    // Eight units of 2k functions each, every unit calling into the next.
    let mut group = c.benchmark_group("resolve_program");
    group.sample_size(10);
    let mut names = Interner::new();
    let unit_names: Vec<Name> = (0..8)
        .map(|i| Name::new(names.intern(&format!("unit{i}"))))
        .collect();
    let units: Vec<Hir> = (0..8u32)
        .map(|u| {
            let next = unit_names[(u as usize + 1) % 8];
            lexical_program(u, 2_000, Some(next), &mut names)
        })
        .collect();
    let total: u64 = units.iter().map(nodes).sum();
    group.throughput(Throughput::Elements(total));
    group.bench_function(BenchmarkId::new("eight_units", total), |bench| {
        bench.iter_batched(
            || units.clone(),
            |units| {
                let mut p = Program::new(Policy::new());
                for (u, hir) in units.into_iter().enumerate() {
                    p.add_unit(Some(unit_names[u]), hir);
                }
                p.resolve(&names).unwrap()
            },
            BatchSize::LargeInput,
        );
    });
    group.finish();
}

fn bench_index(c: &mut Criterion) {
    let mut group = c.benchmark_group("index");
    let mut names = Interner::new();
    let hir = lexical_program(0, 20_000, None, &mut names);
    let unit = hir.unit();
    let res = resolve_lang::resolve(hir, &names).unwrap();
    let index = res.index();
    let refs = index.references_all().len() as u64;
    group.throughput(Throughput::Elements(refs));
    group.bench_function("references_of_every_definition", |bench| {
        bench.iter(|| {
            let mut total = 0usize;
            for d in 0..index.definitions().len() {
                total += index.references(resolve_lang::DefRef::from_index(d)).len();
            }
            total
        });
    });
    group.bench_function("at_every_reference", |bench| {
        bench.iter(|| {
            let mut hits = 0usize;
            for r in index.references_all() {
                hits += usize::from(index.at(unit, r.location.span.start().to_u32()).is_some());
            }
            hits
        });
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_lexical,
    bench_imports,
    bench_program,
    bench_index
);
criterion_main!(benches);
