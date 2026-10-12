//! PHP classes through the `php` preset: a class named where a value goes (the
//! Mox sketch's `new_object` template, `mox.new(Foo, ..)`), and an interface
//! constant reached through an implementing class.
//!
//! Run with `cargo run --example php_classes`.

use hir_lang::{
    Builder, ClassDef, Def, Expr, InterfaceDef, Item, ItemKind, Name, Ns, Path, Res, Segment, Ty,
    Vis,
};
use intern_lang::Interner;
use resolve_lang::{Policy, Resolver};

/// interface Limits { const MAX = 10; }
/// class Foo implements Limits {}
/// function main() { mox.new(Foo); Foo::MAX; }
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut names = Interner::new();
    let mut n = |s: &str| Name::new(names.intern(s));
    let (limits, max, class_name, main_fn) = (n("Limits"), n("MAX"), n("Foo"), n("main"));
    let new_sym = names.intern("mox.new");

    let mut b = Builder::new();
    let ten = b.int(10);
    let max_const = b.item(
        Item::new(
            Some(max),
            ItemKind::Const {
                ty: None,
                value: Some(ten),
            },
        )
        .with_vis(Vis::Public),
    );
    let items = b.list(&[max_const]);
    let interface = b.item(
        Item::new(
            Some(limits),
            ItemKind::Interface(InterfaceDef {
                items,
                ..InterfaceDef::default()
            }),
        )
        .with_vis(Vis::Public),
    );

    // class Foo implements Limits {}
    let limits_path = b.name_path(limits, Ns::Type);
    let limits_ty = b.ty(Ty::Path(limits_path));
    let interfaces = b.list(&[limits_ty]);
    let class = b.item(
        Item::new(
            Some(class_name),
            ItemKind::Class(ClassDef {
                interfaces,
                ..ClassDef::default()
            }),
        )
        .with_vis(Vis::Public),
    );

    // mox.new(Foo): the class is an operand, left for the resolver.
    let callee_path = b.resolved_path(Name::new(new_sym), Ns::Value, Res::Extern(new_sym));
    let callee = b.expr(Expr::Path(callee_path));
    let operand = b.name_expr(class_name);
    let new_foo = b.call(callee, &[operand]);

    // Foo::MAX
    let segs = [
        Segment::new(class_name, b.origin()),
        Segment::new(max, b.origin()),
    ];
    let segs = b.list(&segs);
    let max_path = b.path(Path::new(segs, Ns::Value));
    let class_max = b.expr(Expr::Path(max_path));

    let both = b.list(&[new_foo, class_max]);
    let tuple = b.expr(Expr::Tuple(both));
    let body = b.block(&[], Some(tuple));
    let main_item = b.func(main_fn, &[], body);
    let root = b.module(None, &[interface, class, main_item]);
    let hir = b.finish(root)?;
    let unit = hir.unit();

    let res = Resolver::new(Policy::php()).resolve(hir, &names)?;
    assert!(res.is_clean());
    let hir = res.hir(unit).ok_or("unit")?;

    let Expr::Path(operand_path) = *hir.expr(operand) else {
        return Err("not a path".into());
    };
    let class_def = Res::Def(hir.def(Def::Item(class)));
    assert_eq!(hir.path(operand_path).res, class_def);
    println!("new Foo: the operand resolves to the class item");

    assert_eq!(
        hir.path(max_path).res,
        Res::Def(hir.def(Def::Item(max_const)))
    );
    println!("Foo::MAX: resolves to the interface's constant");
    Ok(())
}
