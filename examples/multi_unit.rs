//! Two units that import from each other, resolved as one program.
//!
//! ```text
//! cargo run --example multi_unit
//! ```

use hir_lang::{Builder, FnDef, Item, ItemId, ItemKind, Name, Ns, Path, Segment, UnitId, Vis};
use intern_lang::Interner;
use resolve_lang::{Policy, Program};

/// `use <other>::<import>;  pub fn <define>() { <import> }`
fn unit(
    id: u32,
    other: Name,
    import: Name,
    define: Name,
) -> Result<(hir_lang::Hir, ItemId), hir_lang::HirError> {
    let mut b = Builder::for_unit(UnitId::new(id));
    let segs = [
        Segment::new(other, b.origin()),
        Segment::new(import, b.origin()),
    ];
    let segs = b.list(&segs);
    let path = b.path(Path::new(segs, Ns::Import));
    let imp = b.item(Item::new(None, ItemKind::Import { path, glob: false }));
    let call = b.name_expr(import);
    let body = b.block(&[], Some(call));
    let f = b.item(
        Item::new(
            Some(define),
            ItemKind::Fn(FnDef {
                body: Some(body),
                ..FnDef::default()
            }),
        )
        .with_vis(Vis::Public),
    );
    let root = b.module(None, &[imp, f]);
    Ok((b.finish(root)?, f))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut names = Interner::new();
    let (a, b) = (Name::new(names.intern("a")), Name::new(names.intern("b")));
    let (ping, pong) = (
        Name::new(names.intern("ping")),
        Name::new(names.intern("pong")),
    );
    // a: use b::pong; pub fn ping() { pong }    b: use a::ping; pub fn pong() { ping }
    let (unit_a, _) = unit(1, b, pong, ping)?;
    let (unit_b, _) = unit(2, a, ping, pong)?;

    let mut program = Program::new(Policy::kraken());
    program.add_unit(Some(a), unit_a);
    program.add_unit(Some(b), unit_b);
    let res = program.resolve(&names)?;
    println!("diagnostics: {}", res.diagnostics().len());
    for def in res.index().definitions() {
        let refs = res
            .index()
            .def_of(def.target)
            .map_or(0, |d| res.index().references(d).len());
        println!(
            "{} {:?}: {} reference(s)",
            def.kind.name(),
            names.resolve(def.name.sym).unwrap_or("?"),
            refs
        );
    }
    Ok(())
}
