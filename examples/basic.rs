//! The lazy path: resolve one unit and print what each name means.
//!
//! ```text
//! cargo run --example basic
//! ```

use hir_lang::{Builder, Expr, Name, Res, Span};
use intern_lang::Interner;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // fn square(n) { n }      fn main() { (square, sqare) }
    let mut names = Interner::new();
    let n = Name::new(names.intern("n"));
    let square = Name::new(names.intern("square"));
    let mut b = Builder::new();
    b.set_span(Span::new(10, 11));
    let (param, _) = b.local_param(n);
    b.set_span(Span::new(15, 16));
    let use_n = b.name_expr(n);
    let body = b.block(&[], Some(use_n));
    let f = b.func(square, &[param], body);
    b.set_span(Span::new(30, 36));
    let ok = b.name_expr(square);
    b.set_span(Span::new(38, 43));
    let typo = b.name_expr(Name::new(names.intern("sqare")));
    let both = b.list(&[ok, typo]);
    let tuple = b.expr(Expr::Tuple(both));
    let main_body = b.block(&[], Some(tuple));
    let main = b.func(Name::new(names.intern("main")), &[], main_body);
    let root = b.module(None, &[f, main]);
    let hir = b.finish(root)?;
    let unit = hir.unit();

    let res = resolve_lang::resolve(hir, &names)?;
    let hir = res.hir(unit).ok_or("unit missing")?;
    for e in [use_n, ok, typo] {
        if let Expr::Path(p) = *hir.expr(e) {
            let what = match hir.path(p).res {
                Res::Local(b) => format!("local {b:?}"),
                Res::Def(d) => format!("definition {d:?}"),
                Res::Err => "error".to_string(),
                other => format!("{other:?}"),
            };
            println!(
                "{:?} -> {what}",
                hir.origin(hir_lang::NodeRef::Path(p)).span
            );
        }
    }
    for d in res.diagnostics() {
        println!("error at {:?}: {}", d.span, d.message(&names));
    }
    Ok(())
}
