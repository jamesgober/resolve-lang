//! What an LSP asks the index: go to definition at a position, find
//! references, the edits of a rename, and the document outline.
//!
//! ```text
//! cargo run --example lsp
//! ```

use hir_lang::{Builder, FnDef, Item, ItemKind, Name, Span};
use intern_lang::Interner;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 0         1         2
    // 0123456789012345678901234567890
    // fn total(x) { x }  fn main() { total }
    let mut names = Interner::new();
    let (total, x) = (
        Name::new(names.intern("total")),
        Name::new(names.intern("x")),
    );
    let mut b = Builder::new();
    b.set_span(Span::new(9, 10));
    let (param, _) = b.local_param(x);
    b.set_span(Span::new(14, 15));
    let use_x = b.name_expr(x);
    let body = b.block(&[], Some(use_x));
    let params = b.list(&[param]);
    let f = b.item(
        Item::new(
            Some(total),
            ItemKind::Fn(FnDef {
                params,
                body: Some(body),
                ..FnDef::default()
            }),
        )
        .with_name_span(Span::new(3, 8)),
    );
    b.set_span(Span::new(31, 36));
    let use_total = b.name_expr(total);
    let main_body = b.block(&[], Some(use_total));
    let main = b.item(
        Item::new(
            Some(Name::new(names.intern("main"))),
            ItemKind::Fn(FnDef {
                body: Some(main_body),
                ..FnDef::default()
            }),
        )
        .with_name_span(Span::new(22, 26)),
    );
    let root = b.module(None, &[f, main]);
    let hir = b.finish(root)?;
    let unit = hir.unit();
    let res = resolve_lang::resolve(hir, &names)?;
    let index = res.index();

    // Go to definition from the use of `total` at offset 33.
    let hit = index.at(unit, 33).ok_or("nothing at 33")?;
    let def = index.definition(hit.def).ok_or("no definition")?;
    println!("definition of the name at 33: {:?}", def.location);
    // Find references and rename.
    println!("references: {}", index.references(hit.def).len());
    println!("rename edits: {:?}", index.rename_set(hit.def).edits);
    // Outline.
    for (_, sym) in index.document_symbols(unit) {
        println!(
            "symbol {} ({})",
            names.resolve(sym.name.sym).unwrap_or("?"),
            sym.kind.name()
        );
    }
    Ok(())
}
