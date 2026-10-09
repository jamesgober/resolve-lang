//! Shared helpers for the integration tests: short constructors over
//! hir-lang's builder.

#![allow(dead_code, clippy::unwrap_used, clippy::expect_used)]

use hir_lang::{
    Arm, Binder, BinderId, BinderKind, Builder, CaptureMode, ClassDef, Closure, Def, DefId, Expr,
    ExprId, FnDef, GenericParam, Generics, Hir, Ident, Item, ItemId, ItemKind, MixinRule,
    MixinUseDef, Name, Ns, Param, ParamId, Pat, PatId, Path, PathId, PathRoot, Res, Segment, Shape,
    Span, Stmt, StmtId, SumDef, Ty, TyId, UnitId, Variant, Vis,
};
use intern_lang::Interner;
use resolve_lang::{DiagKind, Resolution};

pub struct Kit {
    pub names: Interner,
    pub b: Builder,
    pos: u32,
}

impl Kit {
    pub fn new() -> Self {
        Self::for_unit(0, Interner::new())
    }

    pub fn for_unit(unit: u32, names: Interner) -> Self {
        Self {
            names,
            b: Builder::for_unit(UnitId::new(unit)),
            pos: 0,
        }
    }

    /// Starts building a new unit, sharing this kit's interner.
    pub fn start_unit(&mut self, unit: u32) {
        self.b = Builder::for_unit(UnitId::new(unit));
    }

    pub fn name(&mut self, s: &str) -> Name {
        Name::new(self.names.intern(s))
    }

    pub fn ident(&mut self, s: &str) -> Ident {
        let span = self.tick(s.len());
        Ident::new(self.names.intern(s), span)
    }

    /// Advances a fake source position so every name gets a distinct span.
    pub fn tick(&mut self, len: usize) -> Span {
        let start = self.pos;
        self.pos += len as u32 + 1;
        let span = Span::new(start, start + len as u32);
        self.b.set_span(span);
        span
    }

    pub fn segs(&mut self, parts: &[&str]) -> hir_lang::List<Segment> {
        let mut segs = Vec::new();
        for p in parts {
            self.tick(p.len());
            let n = self.name(p);
            segs.push(Segment::new(n, self.b.origin()));
        }
        self.b.list(&segs)
    }

    pub fn path(&mut self, parts: &[&str], ns: Ns) -> PathId {
        let segs = self.segs(parts);
        self.b.path(Path::new(segs, ns))
    }

    pub fn path_root(&mut self, parts: &[&str], ns: Ns, root: PathRoot) -> PathId {
        let segs = self.segs(parts);
        self.b.path(Path {
            root,
            ..Path::new(segs, ns)
        })
    }

    /// A value path expression.
    pub fn use_(&mut self, parts: &[&str]) -> (ExprId, PathId) {
        let p = self.path(parts, Ns::Value);
        (self.b.expr(Expr::Path(p)), p)
    }

    pub fn use_root(&mut self, parts: &[&str], root: PathRoot) -> (ExprId, PathId) {
        let p = self.path_root(parts, Ns::Value, root);
        (self.b.expr(Expr::Path(p)), p)
    }

    pub fn ty(&mut self, parts: &[&str]) -> (TyId, PathId) {
        let p = self.path(parts, Ns::Type);
        (self.b.ty(Ty::Path(p)), p)
    }

    pub fn binder(&mut self, name: &str, kind: BinderKind) -> BinderId {
        self.tick(name.len());
        let n = self.name(name);
        self.b.binder(Binder::new(n, kind))
    }

    pub fn let_(&mut self, name: &str, init: Option<ExprId>) -> (StmtId, BinderId) {
        let b = self.binder(name, BinderKind::Local);
        let pat = self.b.bind(b);
        (self.b.let_stmt(pat, init), b)
    }

    pub fn param(&mut self, name: &str) -> (ParamId, BinderId) {
        let b = self.binder(name, BinderKind::Param);
        let pat = self.b.bind(b);
        (self.b.param(Param::new(pat)), b)
    }

    pub fn stmt(&mut self, e: ExprId) -> StmtId {
        self.b.expr_stmt(e)
    }

    pub fn item_stmt(&mut self, i: ItemId) -> StmtId {
        self.b.stmt(Stmt::Item(i))
    }

    pub fn block(&mut self, stmts: &[StmtId], tail: Option<ExprId>) -> ExprId {
        self.b.block(stmts, tail)
    }

    pub fn tuple(&mut self, xs: &[ExprId]) -> ExprId {
        let l = self.b.list(xs);
        self.b.expr(Expr::Tuple(l))
    }

    pub fn item(&mut self, name: &str, kind: ItemKind, vis: Vis) -> ItemId {
        let span = self.tick(name.len());
        let n = self.name(name);
        self.b
            .item(Item::new(Some(n), kind).with_vis(vis).with_name_span(span))
    }

    pub fn func(&mut self, name: &str, params: &[ParamId], body: ExprId) -> ItemId {
        self.func_vis(name, params, body, Vis::Private)
    }

    pub fn func_vis(&mut self, name: &str, params: &[ParamId], body: ExprId, vis: Vis) -> ItemId {
        let params = self.b.list(params);
        self.item(
            name,
            ItemKind::Fn(FnDef {
                params,
                body: Some(body),
                ..FnDef::default()
            }),
            vis,
        )
    }

    /// `fn name<T..>(params) { body }`.
    pub fn generic_fn(&mut self, name: &str, tparams: &[BinderId], body: ExprId) -> ItemId {
        let gps: Vec<GenericParam> = tparams.iter().map(|b| GenericParam::new(*b)).collect();
        let params = self.b.list(&gps);
        self.item(
            name,
            ItemKind::Fn(FnDef {
                generics: Generics {
                    params,
                    preds: hir_lang::List::EMPTY,
                },
                body: Some(body),
                ..FnDef::default()
            }),
            Vis::Private,
        )
    }

    pub fn constant(&mut self, name: &str, vis: Vis) -> ItemId {
        let one = self.b.int(1);
        self.item(
            name,
            ItemKind::Const {
                ty: None,
                value: Some(one),
            },
            vis,
        )
    }

    pub fn global(&mut self, name: &str, init: Option<ExprId>, vis: Vis) -> ItemId {
        self.item(
            name,
            ItemKind::Global {
                ty: None,
                mutable: true,
                init,
            },
            vis,
        )
    }

    pub fn record(&mut self, name: &str, unit: bool, vis: Vis) -> ItemId {
        self.item(
            name,
            ItemKind::Record(hir_lang::RecordDef {
                shape: if unit { Shape::Unit } else { Shape::Named },
                ..hir_lang::RecordDef::default()
            }),
            vis,
        )
    }

    pub fn sum(
        &mut self,
        name: &str,
        variants: &[(&str, bool)],
        vis: Vis,
    ) -> (ItemId, Vec<hir_lang::VariantId>) {
        let mut vs = Vec::new();
        for (v, unit) in variants {
            let id = self.ident(v);
            vs.push(self.b.variant(Variant {
                name: id,
                shape: if *unit { Shape::Unit } else { Shape::Tuple },
                fields: hir_lang::List::EMPTY,
                discriminant: None,
            }));
        }
        let list = self.b.list(&vs);
        let item = self.item(
            name,
            ItemKind::Sum(SumDef {
                generics: Generics::default(),
                variants: list,
            }),
            vis,
        );
        (item, vs)
    }

    pub fn module(&mut self, name: &str, items: &[ItemId], vis: Vis) -> ItemId {
        let items = self.b.list(items);
        self.item(
            name,
            ItemKind::Module {
                items,
                body: None,
                effects: hir_lang::Effects::NONE,
            },
            vis,
        )
    }

    pub fn class(&mut self, name: &str, bases: &[TyId], items: &[ItemId], mixin: bool) -> ItemId {
        let bases = self.b.list(bases);
        let items = self.b.list(items);
        self.item(
            name,
            ItemKind::Class(ClassDef {
                bases,
                items,
                mixin,
                ..ClassDef::default()
            }),
            Vis::Public,
        )
    }

    pub fn mixin_use(&mut self, mixins: &[TyId], rules: &[MixinRule]) -> ItemId {
        let mixins = self.b.list(mixins);
        let rules = self.b.list(rules);
        self.b.item(Item::new(
            None,
            ItemKind::MixinUse(MixinUseDef { mixins, rules }),
        ))
    }

    /// `use parts as alias` (alias `None`: the last segment's name).
    pub fn import(&mut self, parts: &[&str], alias: Option<&str>, vis: Vis) -> (ItemId, PathId) {
        let path = self.path(parts, Ns::Import);
        let name = alias.map(|a| self.name(a));
        let span = self.tick(alias.map_or(1, str::len));
        let mut item = Item::new(name, ItemKind::Import { path, glob: false }).with_vis(vis);
        if alias.is_some() {
            item = item.with_name_span(span);
        }
        (self.b.item(item), path)
    }

    pub fn import_root(&mut self, parts: &[&str], root: PathRoot, vis: Vis) -> (ItemId, PathId) {
        let path = self.path_root(parts, Ns::Import, root);
        (
            self.b
                .item(Item::new(None, ItemKind::Import { path, glob: false }).with_vis(vis)),
            path,
        )
    }

    pub fn glob(&mut self, parts: &[&str], vis: Vis) -> (ItemId, PathId) {
        let path = self.path(parts, Ns::Import);
        (
            self.b
                .item(Item::new(None, ItemKind::Import { path, glob: true }).with_vis(vis)),
            path,
        )
    }

    /// A closure with implicit by-reference captures.
    pub fn closure(&mut self, params: &[ParamId], body: ExprId) -> ExprId {
        let params = self.b.list(params);
        self.b.expr(Expr::Closure(Closure {
            params,
            implicit: Some(CaptureMode::ByRef),
            ..Closure::new(body)
        }))
    }

    /// `match scrutinee { pat => body, ... }`.
    pub fn matches(&mut self, scrutinee: ExprId, arms: &[(PatId, ExprId)]) -> ExprId {
        let arms: Vec<Arm> = arms
            .iter()
            .map(|(pat, body)| Arm {
                pat: *pat,
                guard: None,
                body: *body,
            })
            .collect();
        let arms = self.b.list(&arms);
        self.b.expr(Expr::Match { scrutinee, arms })
    }

    /// A bare identifier pattern `name` (binds unless it names a constant).
    pub fn ident_pat(&mut self, name: &str) -> (PatId, BinderId, PathId) {
        let b = self.binder(name, BinderKind::Local);
        let path = self.path(&[name], Ns::Pattern);
        (self.b.pat(Pat::Ident { binder: b, path }), b, path)
    }

    pub fn root(&mut self, items: &[ItemId]) -> ItemId {
        self.b.module(None, items)
    }

    pub fn finish(&mut self, items: &[ItemId]) -> Hir {
        let root = self.root(items);
        let b = core::mem::replace(&mut self.b, Builder::new());
        b.finish(root).expect("valid HIR")
    }
}

/// The resolution of a path after resolving.
pub fn res(r: &Resolution, unit: u32, p: PathId) -> (Res, u32) {
    let hir = r.hir(UnitId::new(unit)).expect("unit");
    let path = hir.path(p);
    (path.res, path.unresolved)
}

pub fn item_res(unit: u32, item: ItemId) -> Res {
    Res::Def(DefId::foreign(UnitId::new(unit), Def::Item(item)))
}

pub fn variant_res(unit: u32, v: hir_lang::VariantId) -> Res {
    Res::Def(DefId::foreign(UnitId::new(unit), Def::Variant(v)))
}

/// The diagnostic kinds, in order.
pub fn kinds(r: &Resolution) -> Vec<DiagKind> {
    r.diagnostics().iter().map(|d| d.kind).collect()
}

/// Messages, for readable assertion failures.
pub fn messages(r: &Resolution, names: &Interner) -> Vec<String> {
    r.diagnostics().iter().map(|d| d.message(names)).collect()
}
