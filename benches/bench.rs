//! Criterion benchmarks at realistic scale: whole-unit resolution at about
//! 100k and 1M HIR nodes (also under PHP's case-insensitive tables), an
//! import-heavy multi-module program, a multi-unit program, class
//! hierarchies with several bases (C3) and lexically inherited members, PHP
//! classes (class names as values, interface constants, trait tables), the
//! HIR 0.4 forms (place aliases, keyed yields, union-typed parameters), and
//! index queries.

#![allow(clippy::unwrap_used, clippy::expect_used, missing_docs)]

use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use hir_lang::{
    Binder, BinderKind, Builder, ClassDef, Effects, Expr, ExprId, FnDef, GenericParam, Generics,
    Hir, IdKind, Ident, InterfaceDef, Item, ItemId, ItemKind, MixinAction, MixinRule, MixinUseDef,
    Name, Ns, Param, Path, PathRoot, Res, Segment, Span, Ty, TyId, UnitId, Vis,
};
use intern_lang::Interner;
use resolve_lang::{Policy, Program, Resolver};

/// A unit of `fns` functions, each with two parameters, six `let`s chaining
/// on each other and on the parameters, and calls of other functions; the
/// first one calls into `other` (another unit's root name) when given.
fn lexical_program(unit: u32, fns: usize, other: Option<Name>, names: &mut Interner) -> Hir {
    spelled_program(unit, fns, other, names, false)
}

/// As `lexical_program`; with `php`, functions are declared `Fi` and called
/// as `fi` (found through case folding under `Policy::php()`).
fn spelled_program(
    unit: u32,
    fns: usize,
    other: Option<Name>,
    names: &mut Interner,
    php: bool,
) -> Hir {
    let mut b = Builder::for_unit(UnitId::new(unit));
    let mut pos = 0u32;
    let decl_names: Vec<Name> = (0..fns)
        .map(|i| {
            let s = if php {
                format!("F{i}")
            } else {
                format!("f{i}")
            };
            Name::new(names.intern(&s))
        })
        .collect();
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
    for (i, &fname) in decl_names.iter().enumerate() {
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

fn bench_php(c: &mut Criterion) {
    // The 124k-node unit, declared `Fi` and called `fi`: every call is found
    // through PHP's case-insensitive function table (the fold of the whole
    // interner included).
    let mut group = c.benchmark_group("resolve_php");
    group.sample_size(10);
    let mut names = Interner::new();
    let hir = spelled_program(0, 20_000, None, &mut names, true);
    let n = nodes(&hir);
    group.throughput(Throughput::Elements(n));
    group.bench_function(BenchmarkId::new("case_folded_calls", n), |bench| {
        bench.iter_batched(
            || hir.clone(),
            |h| {
                let r = Resolver::new(Policy::php()).resolve(h, &names).unwrap();
                assert!(r.is_clean());
                r
            },
            BatchSize::LargeInput,
        );
    });
    group.finish();
}

/// `fns` generator functions over the HIR 0.4 forms, Mox style:
/// `fn gi<T, U>(a: T | U | ?R, k) yield { let_place p = a[k] in p =
/// f(p, k); ... yield k => a; yield from f(k) }`, four place aliases per
/// function, with one record `R` and calls of other functions.
fn forms_program(fns: usize, names: &mut Interner) -> Hir {
    let mut b = Builder::new();
    let mut pos = 0u32;
    let mut tick = |b: &mut Builder| {
        pos += 2;
        b.set_span(Span::new(pos, pos + 1));
    };
    let n = |names: &mut Interner, s: &str| Name::new(names.intern(s));
    let (t, u, r, a, k, p) = (
        n(names, "T"),
        n(names, "U"),
        n(names, "R"),
        n(names, "a"),
        n(names, "k"),
        n(names, "p"),
    );
    let fn_names: Vec<Name> = (0..fns).map(|i| n(names, &format!("g{i}"))).collect();
    let path = |b: &mut Builder, name: Name, ns: Ns| {
        let seg = Segment::new(name, b.origin());
        let segs = b.list(&[seg]);
        b.path(Path::new(segs, ns))
    };
    let mut items: Vec<ItemId> = Vec::with_capacity(fns + 1);
    items.push(b.item(Item::new(
        Some(r),
        ItemKind::Record(hir_lang::RecordDef::default()),
    )));
    for (i, &fname) in fn_names.iter().enumerate() {
        let tb = b.binder(Binder::new(t, BinderKind::TypeParam));
        let ub = b.binder(Binder::new(u, BinderKind::TypeParam));
        let gps = b.list(&[GenericParam::new(tb), GenericParam::new(ub)]);
        tick(&mut b);
        let members: Vec<TyId> = [t, u]
            .iter()
            .map(|m| {
                let p = path(&mut b, *m, Ns::Type);
                b.ty(Ty::Path(p))
            })
            .collect();
        let rp = path(&mut b, r, Ns::Type);
        let rt = b.ty(Ty::Path(rp));
        let nr = b.ty(Ty::Nullable(rt));
        let list = b.list(&[members[0], members[1], nr]);
        let ty = b.ty(Ty::Union(list));
        let ab = b.binder(Binder::new(a, BinderKind::Param));
        let apat = b.bind(ab);
        let pa = b.param(Param {
            ty: Some(ty),
            ..Param::new(apat)
        });
        let kb = b.binder(Binder::new(k, BinderKind::Param));
        let kpat = b.bind(kb);
        let pk = b.param(Param::new(kpat));
        let mut stmts = Vec::new();
        for j in 0..4 {
            tick(&mut b);
            let base = b.name_expr(a);
            let index = b.name_expr(k);
            let place = b.expr(Expr::Index { base, index });
            let alias = b.binder(Binder::new(p, BinderKind::Place));
            let target = b.name_expr(p);
            let callee = b.name_expr(fn_names[(i * 31 + j) % fns]);
            let read = b.name_expr(p);
            let kk = b.name_expr(k);
            let value = b.call(callee, &[read, kk]);
            let body = b.expr(Expr::Assign {
                target,
                op: None,
                value,
            });
            let lp = b.expr(Expr::LetPlace {
                binder: alias,
                place,
                body,
            });
            stmts.push(b.expr_stmt(lp));
        }
        let key = b.name_expr(k);
        let value = b.name_expr(a);
        let y = b.expr(Expr::Yield {
            key: Some(key),
            value: Some(value),
        });
        stmts.push(b.expr_stmt(y));
        let callee = b.name_expr(fn_names[(i * 7 + 1) % fns]);
        let kk = b.name_expr(k);
        let inner = b.call(callee, &[kk]);
        let yf = b.expr(Expr::YieldFrom(inner));
        stmts.push(b.expr_stmt(yf));
        let body = b.block(&stmts, None);
        let params = b.list(&[pa, pk]);
        items.push(b.item(Item::new(
            Some(fname),
            ItemKind::Fn(FnDef {
                generics: Generics {
                    params: gps,
                    preds: hir_lang::List::EMPTY,
                },
                params,
                effects: Effects::YIELD,
                body: Some(body),
                ..FnDef::default()
            }),
        )));
    }
    let root = b.module(None, &items);
    b.finish(root).unwrap()
}

fn bench_forms(c: &mut Criterion) {
    let mut group = c.benchmark_group("resolve_hir_0_4_forms");
    group.sample_size(10);
    let mut names = Interner::new();
    let hir = forms_program(2_000, &mut names);
    let n = nodes(&hir);
    group.throughput(Throughput::Elements(n));
    group.bench_function(
        BenchmarkId::new("place_aliases_yields_unions", n),
        |bench| {
            bench.iter_batched(
                || hir.clone(),
                |h| {
                    let r = resolve_lang::resolve(h, &names).unwrap();
                    assert!(r.is_clean());
                    r
                },
                BatchSize::LargeInput,
            );
        },
    );
    group.finish();
}

/// `classes` classes, each with three bases drawn from 40 shallow base
/// classes (Python mixin style, so every C3 order is consistent), a member,
/// and a method naming inherited members unqualified and through the class.
fn class_program(classes: usize, names: &mut Interner) -> Hir {
    let mut b = Builder::new();
    let mut pos = 0u32;
    let mut tick = |b: &mut Builder| {
        pos += 2;
        b.set_span(Span::new(pos, pos + 1));
    };
    let member = |i: usize, names: &mut Interner| Name::new(names.intern(&format!("k{i}")));
    let mut items = Vec::new();
    let base_names: Vec<Name> = (0..40)
        .map(|i| Name::new(names.intern(&format!("B{i}"))))
        .collect();
    for (i, &bn) in base_names.iter().enumerate() {
        let one = b.int(1);
        let k = b.item(
            Item::new(
                Some(member(i, names)),
                ItemKind::Const {
                    ty: None,
                    value: Some(one),
                },
            )
            .with_vis(Vis::Public),
        );
        let list = b.list(&[k]);
        items.push(
            b.item(
                Item::new(
                    Some(bn),
                    ItemKind::Class(ClassDef {
                        items: list,
                        ..ClassDef::default()
                    }),
                )
                .with_vis(Vis::Public),
            ),
        );
    }
    let ty = |b: &mut Builder, n: Name| -> TyId {
        let p = b.name_path(n, Ns::Type);
        b.ty(Ty::Path(p))
    };
    for i in 0..classes {
        let bases: Vec<TyId> = [i % 40, (i * 7 + 3) % 40, (i * 13 + 11) % 40]
            .iter()
            .fold(Vec::new(), |mut v, &x| {
                if !v.contains(&x) {
                    v.push(x);
                }
                v
            })
            .into_iter()
            .map(|x| ty(&mut b, base_names[x]))
            .collect();
        let cname = Name::new(names.intern(&format!("C{i}")));
        let mut uses = Vec::new();
        for x in [i % 40, (i * 7 + 3) % 40, (i * 13 + 11) % 40] {
            tick(&mut b);
            let k = member(x, names);
            uses.push(b.name_expr(k));
            let segs = [Segment::new(cname, b.origin()), Segment::new(k, b.origin())];
            let segs = b.list(&segs);
            let p = b.path(Path::new(segs, Ns::Value));
            uses.push(b.expr(Expr::Path(p)));
        }
        let list = b.list(&uses);
        let t = b.expr(Expr::Tuple(list));
        let body = b.block(&[], Some(t));
        let m = b.func(Name::new(names.intern("method")), &[], body);
        let bases = b.list(&bases);
        let members = b.list(&[m]);
        items.push(
            b.item(
                Item::new(
                    Some(cname),
                    ItemKind::Class(ClassDef {
                        bases,
                        items: members,
                        ..ClassDef::default()
                    }),
                )
                .with_vis(Vis::Public),
            ),
        );
    }
    let root = b.module(None, &items);
    b.finish(root).unwrap()
}

fn bench_classes(c: &mut Criterion) {
    let mut group = c.benchmark_group("resolve_classes");
    group.sample_size(10);
    let mut names = Interner::new();
    let hir = class_program(10_000, &mut names);
    let n = nodes(&hir);
    group.throughput(Throughput::Elements(n));
    group.bench_function(BenchmarkId::new("c3_and_lexical_inheritance", n), |bench| {
        bench.iter_batched(
            || hir.clone(),
            |h| {
                let r = Resolver::new(Policy::kraken()).resolve(h, &names).unwrap();
                assert!(r.is_clean());
                r
            },
            BatchSize::LargeInput,
        );
    });
    group.finish();
}

/// A PHP unit of `classes` classes in chains of 50 (`Ci extends C(i-1)`), each
/// implementing one of 400 interfaces (which extend each other in chains of
/// four), naming classes as values (`mox.new(cj)`, spelled in lower case, the
/// Mox `new_object` operand), reading an interface constant through its class
/// (`Ci::K`), and, for every fifth class, using two of 200 traits with an
/// three `insteadof` and two `as` rules.
fn php_class_program(classes: usize, names: &mut Interner) -> Hir {
    let mut b = Builder::new();
    let mut pos = 0u32;
    let mut tick = |b: &mut Builder| {
        pos += 2;
        b.set_span(Span::new(pos, pos + 1));
    };
    let n = |names: &mut Interner, s: String| Name::new(names.intern(&s));
    let ty = |b: &mut Builder, n: Name| -> TyId {
        let p = b.name_path(n, Ns::Type);
        b.ty(Ty::Path(p))
    };
    let new_sym = names.intern("mox.new");
    let mut items = Vec::new();
    for m in 0..400usize {
        let name = n(names, format!("I{m}"));
        let one = b.int(1);
        let konst = n(names, format!("K{m}"));
        let k = b.item(
            Item::new(
                Some(konst),
                ItemKind::Const {
                    ty: None,
                    value: Some(one),
                },
            )
            .with_vis(Vis::Public),
        );
        let supers: Vec<TyId> = if m % 4 != 0 {
            let sup = n(names, format!("I{}", m - 1));
            vec![ty(&mut b, sup)]
        } else {
            Vec::new()
        };
        let supers = b.list(&supers);
        let members = b.list(&[k]);
        items.push(
            b.item(
                Item::new(
                    Some(name),
                    ItemKind::Interface(InterfaceDef {
                        supers,
                        items: members,
                        ..InterfaceDef::default()
                    }),
                )
                .with_vis(Vis::Public),
            ),
        );
    }
    for t in 0..200usize {
        let name = n(names, format!("T{t}"));
        let mut methods = Vec::new();
        for m in 0..3 {
            let body = b.block(&[], None);
            let mname = n(names, format!("m{m}"));
            methods.push(
                b.item(
                    Item::new(
                        Some(mname),
                        ItemKind::Fn(FnDef {
                            body: Some(body),
                            ..FnDef::default()
                        }),
                    )
                    .with_vis(Vis::Public),
                ),
            );
        }
        let members = b.list(&methods);
        items.push(
            b.item(
                Item::new(
                    Some(name),
                    ItemKind::Class(ClassDef {
                        items: members,
                        mixin: true,
                        ..ClassDef::default()
                    }),
                )
                .with_vis(Vis::Public),
            ),
        );
    }
    for i in 0..classes {
        let cname = n(names, format!("C{i}"));
        let mut own = Vec::new();
        // The body: two class operands of `mox.new` and an interface constant.
        tick(&mut b);
        let callee_path = b.resolved_path(Name::new(new_sym), Ns::Value, Res::Extern(new_sym));
        let callee = b.expr(Expr::Path(callee_path));
        let target = n(names, format!("c{}", (i * 7 + 1) % classes));
        let operand = b.name_expr(target);
        let new_a = b.call(callee, &[operand]);
        let callee_path = b.resolved_path(Name::new(new_sym), Ns::Value, Res::Extern(new_sym));
        let callee = b.expr(Expr::Path(callee_path));
        let other = n(names, format!("C{}", (i + 1) % classes));
        let operand = b.name_expr(other);
        let new_b = b.call(callee, &[operand]);
        let konst = n(names, format!("K{}", i % 400));
        let segs = [
            Segment::new(cname, b.origin()),
            Segment::new(konst, b.origin()),
        ];
        let segs = b.list(&segs);
        let p = b.path(Path::new(segs, Ns::Value));
        let through = b.expr(Expr::Path(p));
        let list = b.list(&[new_a, new_b, through]);
        let t = b.expr(Expr::Tuple(list));
        let body = b.block(&[], Some(t));
        let method = n(names, "method".to_string());
        own.push(
            b.item(
                Item::new(
                    Some(method),
                    ItemKind::Fn(FnDef {
                        body: Some(body),
                        ..FnDef::default()
                    }),
                )
                .with_vis(Vis::Public),
            ),
        );
        if i % 5 == 0 {
            // use Ta, Tb { Ta::m0/m1/m2 insteadof Tb; Tb::m1 as protected; Tb::m2 as extra; }
            let ta = i % 200;
            let mut tb = (i * 3 + 1) % 200;
            if ta == tb {
                tb = (tb + 1) % 200;
            }
            let (na, nb) = (n(names, format!("T{ta}")), n(names, format!("T{tb}")));
            let tys = [ty(&mut b, na), ty(&mut b, nb)];
            let mixins = b.list(&tys);
            let others = [ty(&mut b, nb)];
            let others = b.list(&others);
            let others1 = [ty(&mut b, nb)];
            let others1 = b.list(&others1);
            let others2 = [ty(&mut b, nb)];
            let others2 = b.list(&others2);
            let (from_a1, from_a2) = (ty(&mut b, na), ty(&mut b, na));
            let m0 = n(names, "m0".to_string());
            let m1 = n(names, "m1".to_string());
            let m2 = n(names, "m2".to_string());
            let extra = n(names, "extra".to_string());
            let from_a = ty(&mut b, na);
            let from_b = ty(&mut b, nb);
            let from_b2 = ty(&mut b, nb);
            let rules = [
                MixinRule {
                    method: Ident::new(m0.sym, Span::empty(0)),
                    from: Some(from_a),
                    action: MixinAction::Insteadof(others),
                },
                MixinRule {
                    method: Ident::new(m1.sym, Span::empty(0)),
                    from: Some(from_a1),
                    action: MixinAction::Insteadof(others1),
                },
                MixinRule {
                    method: Ident::new(m2.sym, Span::empty(0)),
                    from: Some(from_a2),
                    action: MixinAction::Insteadof(others2),
                },
                MixinRule {
                    method: Ident::new(m1.sym, Span::empty(0)),
                    from: Some(from_b),
                    action: MixinAction::Alias {
                        name: None,
                        vis: Some(Vis::Protected),
                    },
                },
                MixinRule {
                    method: Ident::new(m2.sym, Span::empty(0)),
                    from: Some(from_b2),
                    action: MixinAction::Alias {
                        name: Some(Ident::new(extra.sym, Span::empty(0))),
                        vis: None,
                    },
                },
            ];
            let rules = b.list(&rules);
            own.push(b.item(Item::new(
                None,
                ItemKind::MixinUse(MixinUseDef { mixins, rules }),
            )));
        }
        let base: Vec<TyId> = if i % 50 != 0 {
            let bn = n(names, format!("C{}", i - 1));
            vec![ty(&mut b, bn)]
        } else {
            Vec::new()
        };
        let iface = n(names, format!("I{}", i % 400));
        let ifaces = [ty(&mut b, iface)];
        let bases = b.list(&base);
        let interfaces = b.list(&ifaces);
        let members = b.list(&own);
        items.push(
            b.item(
                Item::new(
                    Some(cname),
                    ItemKind::Class(ClassDef {
                        bases,
                        interfaces,
                        items: members,
                        ..ClassDef::default()
                    }),
                )
                .with_vis(Vis::Public),
            ),
        );
    }
    let root = b.module(None, &items);
    b.finish(root).unwrap()
}

fn bench_php_classes(c: &mut Criterion) {
    // Class names as values, interface constants through classes, and trait
    // tables with rules, in one 10,000-class unit under `Policy::php()`.
    let mut group = c.benchmark_group("resolve_php_classes");
    group.sample_size(10);
    let mut names = Interner::new();
    let hir = php_class_program(10_000, &mut names);
    let n = nodes(&hir);
    group.throughput(Throughput::Elements(n));
    group.bench_function(
        BenchmarkId::new("class_values_interface_constants_mixins", n),
        |bench| {
            bench.iter_batched(
                || hir.clone(),
                |h| {
                    let r = Resolver::new(Policy::php()).resolve(h, &names).unwrap();
                    assert!(
                        r.is_clean(),
                        "{:?}",
                        r.diagnostics()
                            .iter()
                            .take(3)
                            .map(|d| d.message(&names))
                            .collect::<Vec<_>>()
                    );
                    r
                },
                BatchSize::LargeInput,
            );
        },
    );
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
    bench_php,
    bench_classes,
    bench_php_classes,
    bench_forms,
    bench_index
);
criterion_main!(benches);
