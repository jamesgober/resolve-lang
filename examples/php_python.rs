//! PHP and Python name semantics through their presets: PHP's
//! case-insensitive functions and classes beside its case-sensitive constant
//! table, and Python's C3 method resolution order.
//!
//! Run with `cargo run --example php_python`.

use hir_lang::{
    Builder, ClassDef, Expr, FnDef, Item, ItemKind, Name, Ns, Path, Segment, Ty, TyId, Vis,
};
use intern_lang::Interner;
use resolve_lang::{Policy, Resolver};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    php()?;
    python()?;
    Ok(())
}

/// function strLen() {}   const LIMIT = 1;   const strlen = 2;
/// function main() { STRLEN(); strlen; LIMIT; limit; }
fn php() -> Result<(), Box<dyn std::error::Error>> {
    let mut names = Interner::new();
    let mut n = |s: &str| Name::new(names.intern(s));
    let (strlen_decl, limit, strlen_const) = (n("strLen"), n("LIMIT"), n("strlen"));
    let (strlen_upper, limit_lower, main) = (n("STRLEN"), n("limit"), n("main"));
    let mut b = Builder::new();
    let body = b.block(&[], None);
    let f = b.item(
        Item::new(
            Some(strlen_decl),
            ItemKind::Fn(FnDef {
                body: Some(body),
                ..FnDef::default()
            }),
        )
        .with_vis(Vis::Public),
    );
    let one = b.int(1);
    let c1 = b.item(Item::new(
        Some(limit),
        ItemKind::Const {
            ty: None,
            value: Some(one),
        },
    ));
    let two = b.int(2);
    let c2 = b.item(Item::new(
        Some(strlen_const),
        ItemKind::Const {
            ty: None,
            value: Some(two),
        },
    ));
    let callee = b.name_expr(strlen_upper);
    let call = b.call(callee, &[]);
    let as_value = b.name_expr(strlen_const);
    let lim = b.name_expr(limit);
    let wrong = b.name_expr(limit_lower);
    let list = b.list(&[call, as_value, lim, wrong]);
    let t = b.expr(Expr::Tuple(list));
    let main_body = b.block(&[], Some(t));
    let m = b.func(main, &[], main_body);
    let root = b.module(None, &[f, c1, c2, m]);
    let res = Resolver::new(Policy::php()).resolve(b.finish(root)?, &names)?;
    println!("PHP:");
    for d in res.diagnostics() {
        println!("  {}", d.message(&names));
    }
    // `STRLEN()` found the function, `strlen` the constant, `LIMIT` the
    // constant; only `limit` (constants keep case) is reported.
    assert_eq!(res.diagnostics().len(), 1);
    Ok(())
}

/// class O   class A(O): x = 1   class B(O): x = 2   class C(A, B)
/// class Bad(O, A)                                  (inconsistent: Python's TypeError)
/// def main(): C.x                                  (A.x, by C3: C, A, B, O)
fn python() -> Result<(), Box<dyn std::error::Error>> {
    let mut names = Interner::new();
    let mut b = Builder::new();
    let mut class = |b: &mut Builder, name: &str, bases: &[&str], x: bool| {
        let tys: Vec<TyId> = bases
            .iter()
            .map(|s| {
                let p = b.name_path(Name::new(names.intern(s)), Ns::Type);
                b.ty(Ty::Path(p))
            })
            .collect();
        let mut items = Vec::new();
        if x {
            let one = b.int(1);
            items.push(b.item(Item::new(
                Some(Name::new(names.intern("x"))),
                ItemKind::Const {
                    ty: None,
                    value: Some(one),
                },
            )));
        }
        let bases = b.list(&tys);
        let items = b.list(&items);
        b.item(Item::new(
            Some(Name::new(names.intern(name))),
            ItemKind::Class(ClassDef {
                bases,
                items,
                ..ClassDef::default()
            }),
        ))
    };
    let o = class(&mut b, "O", &[], false);
    let a = class(&mut b, "A", &["O"], true);
    let bb = class(&mut b, "B", &["O"], true);
    let c = class(&mut b, "C", &["A", "B"], false);
    let bad = class(&mut b, "Bad", &["O", "A"], false);
    let segs = [
        Segment::new(Name::new(names.intern("C")), b.origin()),
        Segment::new(Name::new(names.intern("x")), b.origin()),
    ];
    let segs = b.list(&segs);
    let path = b.path(Path::new(segs, Ns::Value));
    let use_cx = b.expr(Expr::Path(path));
    let body = b.block(&[], Some(use_cx));
    let main = b.func(Name::new(names.intern("main")), &[], body);
    let root = b.module(None, &[o, a, bb, c, bad, main]);
    let hir = b.finish(root)?;
    let unit = hir.unit();
    let res = Resolver::new(Policy::python()).resolve(hir, &names)?;
    println!("Python:");
    for d in res.diagnostics() {
        println!("  {}", d.message(&names));
    }
    let resolved = res.hir(unit).map(|h| h.path(path).res);
    println!("  C.x resolves to {resolved:?}");
    assert_eq!(res.diagnostics().len(), 1);
    Ok(())
}
