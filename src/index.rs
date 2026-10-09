//! The persistent definition/reference index: the data an LSP needs for
//! go-to-definition, find-references, rename, and document symbols.
//!
//! Built once per resolution and owned by the [`Resolution`](crate::Resolution).
//! Every lookup is by dense id: definitions and references are vectors, the
//! references of a definition are one contiguous slice (CSR layout), and
//! per-unit side tables are keyed by HIR item, variant, binder, and path ids.

use alloc::vec::Vec;

use hir_lang::{
    BinderId, BinderKind, Def, DefId, ExpnId, Hir, IdKind, ItemId, ItemKind, Name, NodeRef, Origin,
    PathId, Span, Symbol, UnitId, VariantId,
};

use crate::model::{NONE, ix};

/// What kind of thing a definition is, for symbol lists and icons.
///
/// # Examples
///
/// ```
/// use resolve_lang::SymbolKind;
///
/// assert_eq!(SymbolKind::Function.name(), "function");
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SymbolKind {
    /// A module.
    Module,
    /// A function or method.
    Function,
    /// A record.
    Record,
    /// A sum.
    Sum,
    /// A sum variant.
    Variant,
    /// A class.
    Class,
    /// A mixin (PHP trait).
    Mixin,
    /// An interface.
    Interface,
    /// An impl block.
    Impl,
    /// A type alias.
    Alias,
    /// An associated type.
    AssocType,
    /// A constant.
    Const,
    /// A global.
    Global,
    /// An aliased import (`use x as y`): `y` is renameable on its own.
    Import,
    /// A local variable.
    Local,
    /// A parameter.
    Param,
    /// An explicit capture or a closure's self binder.
    Capture,
    /// A type parameter.
    TypeParam,
    /// A const parameter.
    ConstParam,
    /// A region parameter.
    Region,
    /// A loop or block label.
    Label,
    /// Something outside the program (another package, a host symbol): it
    /// has references but no location.
    External,
}

impl SymbolKind {
    /// A short lowercase name.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::SymbolKind;
    ///
    /// assert_eq!(SymbolKind::TypeParam.name(), "type parameter");
    /// ```
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Module => "module",
            Self::Function => "function",
            Self::Record => "record",
            Self::Sum => "sum",
            Self::Variant => "variant",
            Self::Class => "class",
            Self::Mixin => "mixin",
            Self::Interface => "interface",
            Self::Impl => "impl",
            Self::Alias => "alias",
            Self::AssocType => "associated type",
            Self::Const => "constant",
            Self::Global => "global",
            Self::Import => "import",
            Self::Local => "local",
            Self::Param => "parameter",
            Self::Capture => "capture",
            Self::TypeParam => "type parameter",
            Self::ConstParam => "const parameter",
            Self::Region => "region",
            Self::Label => "label",
            Self::External => "external",
        }
    }

    const fn of_item(kind: &ItemKind) -> Self {
        match kind {
            ItemKind::Fn(_) => Self::Function,
            ItemKind::Record(_) => Self::Record,
            ItemKind::Sum(_) => Self::Sum,
            ItemKind::Class(c) if c.mixin => Self::Mixin,
            ItemKind::Class(_) => Self::Class,
            ItemKind::Interface(_) => Self::Interface,
            ItemKind::Impl(_) => Self::Impl,
            ItemKind::Alias { .. } => Self::Alias,
            ItemKind::AssocType { .. } => Self::AssocType,
            ItemKind::Const { .. } => Self::Const,
            ItemKind::Global { .. } => Self::Global,
            ItemKind::Module { .. } | ItemKind::Err => Self::Module,
            ItemKind::Import { .. } | ItemKind::MixinUse(_) => Self::Import,
        }
    }

    const fn of_binder(kind: BinderKind) -> Self {
        match kind {
            BinderKind::Local => Self::Local,
            BinderKind::Param => Self::Param,
            BinderKind::Capture => Self::Capture,
            BinderKind::TypeParam => Self::TypeParam,
            BinderKind::ConstParam => Self::ConstParam,
            BinderKind::Region => Self::Region,
            BinderKind::Label => Self::Label,
        }
    }
}

/// What a definition is, as an identity that survives across units.
///
/// # Examples
///
/// ```
/// use hir_lang::{BinderId, UnitId};
/// use resolve_lang::Target;
///
/// let t = Target::Local(UnitId::new(0), BinderId::from_index(3).unwrap());
/// assert!(matches!(t, Target::Local(..)));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Target {
    /// An item or variant.
    Def(DefId),
    /// A binder of a unit.
    Local(UnitId, BinderId),
    /// A host symbol.
    Extern(Symbol),
    /// An aliased import item (its own name is the definition).
    Import(UnitId, ItemId),
}

/// A place in the source.
///
/// # Examples
///
/// ```
/// use hir_lang::{Span, UnitId};
/// use resolve_lang::Location;
///
/// let l = Location { unit: UnitId::new(1), span: Span::new(4, 7), in_source: true };
/// assert_eq!(l.span.len(), 3);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    /// The unit.
    pub unit: UnitId,
    /// The span. For a name that came out of a macro or template expansion,
    /// this is the outermost expansion's call site.
    pub span: Span,
    /// Whether the name was written in the source (its origin is not an
    /// expansion). Only such names are rename edits.
    pub in_source: bool,
}

/// An opaque handle to a definition in an [`Index`].
///
/// # Examples
///
/// ```
/// use resolve_lang::DefRef;
///
/// assert_eq!(DefRef::from_index(5).index(), 5);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefRef(u32);

impl DefRef {
    /// The dense position of the definition.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::DefRef;
    ///
    /// assert_eq!(DefRef::from_index(0).index(), 0);
    /// ```
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    /// A handle from a dense position (saturating past `u32::MAX`).
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::DefRef;
    ///
    /// assert_eq!(DefRef::from_index(9), DefRef::from_index(9));
    /// ```
    #[must_use]
    pub const fn from_index(i: usize) -> Self {
        Self(if i > u32::MAX as usize {
            u32::MAX
        } else {
            i as u32
        })
    }
}

/// One definition.
///
/// # Examples
///
/// ```
/// use hir_lang::{Builder, Name};
/// use intern_lang::Interner;
/// use resolve_lang::SymbolKind;
///
/// let mut names = Interner::new();
/// let mut b = Builder::new();
/// let body = b.block(&[], None);
/// let f = b.func(Name::new(names.intern("f")), &[], body);
/// let root = b.module(None, &[f]);
/// let res = resolve_lang::resolve(b.finish(root)?, &names)?;
/// let def = res.index().definitions().iter().find(|d| d.kind == SymbolKind::Function).unwrap();
/// assert_eq!(names.resolve(def.name.sym), Some("f"));
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Definition {
    /// What it is.
    pub target: Target,
    /// Its name.
    pub name: Name,
    /// Its kind.
    pub kind: SymbolKind,
    /// Where its name is: `None` for something outside the program, and for
    /// an item whose lowering recorded no name span (use `range` then).
    pub location: Option<Location>,
    /// The span of the whole definition (an item's or binder's own span).
    pub range: Option<Location>,
    /// The enclosing item's definition, for symbol trees.
    pub parent: Option<DefRef>,
}

/// One resolved name in a path.
///
/// # Examples
///
/// ```
/// use resolve_lang::Reference;
///
/// fn first_segment(r: &Reference) -> bool { r.segment == 0 }
/// # let _ = first_segment;
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reference {
    /// Where the name is.
    pub location: Location,
    /// What it resolves to.
    pub def: DefRef,
    /// The path holding it.
    pub path: PathId,
    /// The segment of the path.
    pub segment: u32,
    /// The name as written (differs from the definition's name when reached
    /// through an aliased import).
    pub name: Name,
    /// The aliased import the name was reached through, if any.
    pub via: Option<DefRef>,
}

/// What [`Index::at`] found at a position.
///
/// # Examples
///
/// ```
/// use resolve_lang::{DefRef, Occurrence};
///
/// let o = Occurrence { def: DefRef::from_index(0), reference: None };
/// assert!(o.is_definition());
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Occurrence {
    /// The definition named there.
    pub def: DefRef,
    /// The reference there (by position in [`Index::references_all`]), or
    /// `None` if the position is the definition's own name.
    pub reference: Option<u32>,
}

impl Occurrence {
    /// Whether the position is the definition's own name.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{DefRef, Occurrence};
    ///
    /// let o = Occurrence { def: DefRef::from_index(0), reference: Some(3) };
    /// assert!(!o.is_definition());
    /// ```
    #[must_use]
    pub const fn is_definition(&self) -> bool {
        self.reference.is_none()
    }
}

/// The references to one definition, in location order: see
/// [`Index::references`].
///
/// # Examples
///
/// ```
/// use resolve_lang::{DefRef, Index};
///
/// let index = Index::default();
/// let mut refs = index.references(DefRef::from_index(3));
/// assert!(refs.next().is_none());
/// ```
#[derive(Clone, Debug)]
pub struct References<'a> {
    refs: &'a [Reference],
    ids: core::slice::Iter<'a, u32>,
}

impl<'a> Iterator for References<'a> {
    type Item = &'a Reference;

    fn next(&mut self) -> Option<&'a Reference> {
        // Every id is a valid position by construction (the CSR is built
        // from `refs` itself); `get` keeps a corrupted index from panicking.
        self.ids.find_map(|i| self.refs.get(*i as usize))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.ids.len(), Some(self.ids.len()))
    }
}

impl ExactSizeIterator for References<'_> {}

/// The edits a rename of one definition makes.
///
/// # Examples
///
/// ```
/// use resolve_lang::RenameSet;
///
/// let r = RenameSet::default();
/// assert!(r.edits.is_empty() && r.outside_source.is_empty());
/// ```
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RenameSet {
    /// Every occurrence written in the source, the definition's name
    /// included, sorted by location.
    pub edits: Vec<Location>,
    /// Occurrences produced by expansions: a rename cannot edit them
    /// directly (the macro or template that produced them needs a look).
    pub outside_source: Vec<Location>,
}

/// Per-unit side tables.
#[derive(Clone, Debug, Default)]
struct UnitIx {
    id: UnitId,
    item_def: Vec<u32>,
    variant_def: Vec<u32>,
    binder_def: Vec<u32>,
    /// CSR over paths: references of path `p` are `refs[path_off[p]..path_off[p+1]]`.
    path_off: Vec<u32>,
    /// Item definitions in preorder.
    symbols: Vec<u32>,
    /// (start, end, def, reference or NONE), sorted by (start, end).
    occ: Vec<(u32, u32, u32, u32)>,
}

/// The persistent definition/reference index of a resolved program.
///
/// # Examples
///
/// ```
/// use hir_lang::{Builder, Name, Span};
/// use intern_lang::Interner;
///
/// // fn f(n) { n }  — the use of `n` is a reference to the parameter.
/// let mut names = Interner::new();
/// let n = Name::new(names.intern("n"));
/// let mut b = Builder::new();
/// b.set_span(Span::new(5, 6));
/// let (param, _) = b.local_param(n);
/// b.set_span(Span::new(10, 11));
/// let use_n = b.name_expr(n);
/// let body = b.block(&[], Some(use_n));
/// let f = b.func(Name::new(names.intern("f")), &[param], body);
/// let root = b.module(None, &[f]);
/// let hir = b.finish(root)?;
/// let unit = hir.unit();
///
/// let res = resolve_lang::resolve(hir, &names)?;
/// let index = res.index();
/// let hit = index.at(unit, 10).unwrap();
/// let def = index.definition(hit.def).unwrap();
/// assert_eq!(def.location.unwrap().span, Span::new(5, 6));
/// assert_eq!(index.references(hit.def).len(), 1);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[derive(Clone, Debug, Default)]
pub struct Index {
    defs: Vec<Definition>,
    refs: Vec<Reference>,
    by_def_off: Vec<u32>,
    by_def: Vec<u32>,
    /// (aliased-import definition, reference), sorted.
    by_via: Vec<(u32, u32)>,
    /// External definitions by target, sorted.
    externals: Vec<(Target, u32)>,
    units: Vec<UnitIx>,
}

/// Maps an origin to a source location, through expansions.
struct Mapper {
    unit: UnitId,
    /// By expansion id (1-based): the outermost call site.
    sites: Vec<Span>,
}

impl Mapper {
    fn new(hir: &Hir) -> Self {
        let n = hir.count(IdKind::Expansion);
        let mut sites: Vec<Span> = Vec::with_capacity(n);
        for i in 1..=n {
            let e = hir.expansion(ExpnId::from_u32(ix(i)));
            let site = match e {
                Some(e) if e.parent.is_root() => e.call_site,
                Some(e) => sites
                    .get((e.parent.as_u32() as usize).saturating_sub(1))
                    .copied()
                    .unwrap_or(e.call_site),
                None => Span::empty(0),
            };
            sites.push(site);
        }
        Self {
            unit: hir.unit(),
            sites,
        }
    }

    fn map(&self, origin: Origin) -> Location {
        self.span(origin.span, origin.expn)
    }

    fn span(&self, span: Span, expn: ExpnId) -> Location {
        if expn.is_root() {
            return Location {
                unit: self.unit,
                span,
                in_source: true,
            };
        }
        let site = self
            .sites
            .get((expn.as_u32() as usize).saturating_sub(1))
            .copied()
            .unwrap_or(span);
        Location {
            unit: self.unit,
            span: site,
            in_source: false,
        }
    }
}

/// A reference waiting to be indexed: (path, segment, target, via import
/// target).
pub(crate) struct RawRef {
    pub(crate) path: PathId,
    pub(crate) seg: u32,
    pub(crate) target: Target,
    pub(crate) via: Option<Target>,
}

/// The input of one unit to the index build.
pub(crate) struct UnitInput<'a> {
    pub(crate) hir: &'a Hir,
    pub(crate) refs: Vec<RawRef>,
    /// `Pat::Ident` binders that did not bind (their path named a constant).
    pub(crate) dead_binders: Vec<BinderId>,
    /// Aliased import items.
    pub(crate) aliases: Vec<ItemId>,
}

impl Index {
    /// Builds the index of a whole program.
    pub(crate) fn build(units: &[UnitInput<'_>]) -> Self {
        let mut me = Self::default();
        let mut maps: Vec<Mapper> = Vec::with_capacity(units.len());
        for u in units {
            maps.push(Mapper::new(u.hir));
            me.units.push(UnitIx {
                id: u.hir.unit(),
                item_def: alloc::vec![NONE; u.hir.count(IdKind::Item)],
                variant_def: alloc::vec![NONE; u.hir.count(IdKind::Variant)],
                binder_def: alloc::vec![NONE; u.hir.count(IdKind::Binder)],
                path_off: Vec::new(),
                symbols: Vec::new(),
                occ: Vec::new(),
            });
        }
        for (ui, u) in units.iter().enumerate() {
            let Some(map) = maps.get(ui) else { continue };
            me.collect_defs(ui, u, map);
        }
        // External definitions are created on first reference; keep them
        // findable by target.
        let mut externals: Vec<(Target, u32)> = Vec::new();
        let mut by_via: Vec<(u32, u32)> = Vec::new();
        for (ui, u) in units.iter().enumerate() {
            let Some(map) = maps.get(ui) else { continue };
            let mut refs: Vec<&RawRef> = u.refs.iter().collect();
            refs.sort_by_key(|r| (r.path, r.seg));
            refs.dedup_by_key(|r| (r.path, r.seg));
            let n_paths = u.hir.count(IdKind::Path);
            let mut off: Vec<u32> = alloc::vec![0; n_paths + 1];
            for r in refs {
                let path = u.hir.path(r.path);
                let Some(seg) = u.hir.list(path.segments).get(r.seg as usize) else {
                    continue;
                };
                let Some(def) = me.target_def(r.target, seg.name, &mut externals) else {
                    continue;
                };
                let via = r.via.and_then(|t| me.find_target(t, &externals));
                if let Some(v) = via {
                    by_via.push((v.0, ix(me.refs.len())));
                }
                let reference = Reference {
                    location: map.map(seg.origin),
                    def: DefRef(def),
                    path: r.path,
                    segment: r.seg,
                    name: seg.name,
                    via,
                };
                if let Some(o) = off.get_mut(r.path.index() + 1) {
                    *o += 1;
                }
                me.refs.push(reference);
            }
            // Prefix sums turn counts into offsets relative to this unit's
            // first reference.
            let base = ix(me.refs.len()) - off.iter().sum::<u32>();
            let mut acc = base;
            for o in &mut off {
                acc += *o;
                *o = acc;
            }
            if let Some(slot) = me.units.get_mut(ui) {
                slot.path_off = off;
            }
        }
        by_via.sort_unstable();
        me.by_via = by_via;
        me.externals = externals;
        me.build_by_def();
        me.build_occurrences();
        me
    }

    fn push_def(&mut self, d: Definition) -> u32 {
        let i = ix(self.defs.len());
        self.defs.push(d);
        i
    }

    fn collect_defs(&mut self, ui: usize, u: &UnitInput<'_>, map: &Mapper) {
        let hir = u.hir;
        let unit = hir.unit();
        let mut stack: Vec<u32> = Vec::new();
        let mut dead = u.dead_binders.clone();
        dead.sort();
        let mut symbols: Vec<u32> = Vec::new();
        let mut items: Vec<(ItemId, u32)> = Vec::new();
        let mut variants: Vec<(VariantId, u32)> = Vec::new();
        let mut binders: Vec<(BinderId, u32)> = Vec::new();
        let root = hir.root();
        let mut defs_out: Vec<Definition> = Vec::new();
        let base = ix(self.defs.len());
        hir.walk_from(NodeRef::Item(root), |ev| {
            match ev {
                hir_lang::Event::Enter(NodeRef::Item(i)) => {
                    let item = hir.item(i);
                    let alias = u.aliases.binary_search(&i).is_ok();
                    let named = item.name.filter(|_| {
                        !matches!(item.kind, ItemKind::Import { .. } | ItemKind::MixinUse(_))
                            || alias
                    });
                    match named {
                        Some(name) if i != root || item.name.is_some() => {
                            let target = if alias {
                                Target::Import(unit, i)
                            } else {
                                Target::Def(DefId::foreign(unit, Def::Item(i)))
                            };
                            let d = base + ix(defs_out.len());
                            defs_out.push(Definition {
                                target,
                                name,
                                kind: if alias {
                                    SymbolKind::Import
                                } else {
                                    SymbolKind::of_item(&item.kind)
                                },
                                // Lowering that leaves the name span unset
                                // gives no name location (the range still
                                // locates the item).
                                location: (item.name_span != Span::empty(0)).then(|| {
                                    map.span(item.name_span, hir.origin(NodeRef::Item(i)).expn)
                                }),
                                range: Some(map.map(hir.origin(NodeRef::Item(i)))),
                                parent: stack.last().copied().filter(|p| *p != NONE).map(DefRef),
                            });
                            items.push((i, d));
                            symbols.push(d);
                            stack.push(d);
                            if let ItemKind::Sum(sum) = item.kind {
                                for &v in hir.list(sum.variants) {
                                    let Some(var) = hir.variant(v) else { continue };
                                    let vd = base + ix(defs_out.len());
                                    let origin = hir.origin(NodeRef::Variant(v));
                                    defs_out.push(Definition {
                                        target: Target::Def(DefId::foreign(unit, Def::Variant(v))),
                                        name: Name::new(var.name.sym),
                                        kind: SymbolKind::Variant,
                                        location: Some(map.span(var.name.span, origin.expn)),
                                        range: Some(map.map(origin)),
                                        parent: Some(DefRef(d)),
                                    });
                                    variants.push((v, vd));
                                    symbols.push(vd);
                                }
                            }
                        }
                        _ => stack.push(NONE),
                    }
                }
                hir_lang::Event::Leave(NodeRef::Item(_)) => {
                    let _ = stack.pop();
                }
                hir_lang::Event::Bind(b) => {
                    if dead.binary_search(&b).is_ok() {
                        return hir_lang::Control::Continue;
                    }
                    let Some(binder) = hir.binder(b) else {
                        return hir_lang::Control::Continue;
                    };
                    let origin = hir.binder_origin(b);
                    let d = base + ix(defs_out.len());
                    defs_out.push(Definition {
                        target: Target::Local(unit, b),
                        name: binder.name,
                        kind: SymbolKind::of_binder(binder.kind),
                        location: Some(map.map(origin)),
                        range: Some(map.map(origin)),
                        parent: stack.iter().rev().copied().find(|p| *p != NONE).map(DefRef),
                    });
                    binders.push((b, d));
                }
                _ => {}
            }
            hir_lang::Control::Continue
        });
        self.defs.extend(defs_out);
        if let Some(slot) = self.units.get_mut(ui) {
            for (i, d) in items {
                if let Some(x) = slot.item_def.get_mut(i.index()) {
                    *x = d;
                }
            }
            for (v, d) in variants {
                if let Some(x) = slot.variant_def.get_mut(v.index()) {
                    *x = d;
                }
            }
            for (b, d) in binders {
                if let Some(x) = slot.binder_def.get_mut(b.index()) {
                    *x = d;
                }
            }
            slot.symbols = symbols;
        }
    }

    fn unit_ix(&self, unit: UnitId) -> Option<&UnitIx> {
        self.units.iter().find(|u| u.id == unit)
    }

    fn find_target(&self, t: Target, externals: &[(Target, u32)]) -> Option<DefRef> {
        let local = match t {
            Target::Def(d) => self.unit_ix(d.unit()).and_then(|u| match d.def() {
                Def::Item(i) => u.item_def.get(i.index()).copied(),
                Def::Variant(v) => u.variant_def.get(v.index()).copied(),
            }),
            Target::Local(unit, b) => self
                .unit_ix(unit)
                .and_then(|u| u.binder_def.get(b.index()).copied()),
            Target::Import(unit, i) => self
                .unit_ix(unit)
                .and_then(|u| u.item_def.get(i.index()).copied()),
            Target::Extern(_) => None,
        };
        match local.filter(|d| *d != NONE) {
            Some(d) => Some(DefRef(d)),
            None => externals
                .binary_search_by(|(x, _)| x.cmp(&t))
                .ok()
                .and_then(|i| externals.get(i))
                .map(|(_, d)| DefRef(*d)),
        }
    }

    /// The definition of a target, creating an external one (named as the
    /// reference spells it) if needed.
    fn target_def(
        &mut self,
        t: Target,
        spelled: Name,
        externals: &mut Vec<(Target, u32)>,
    ) -> Option<u32> {
        if let Some(d) = self.find_target(t, externals) {
            return Some(d.0);
        }
        let name = match t {
            // A program target with no definition entry (an unnamed item):
            // nothing to point at.
            Target::Def(d) if self.unit_ix(d.unit()).is_some() => return None,
            Target::Local(..) | Target::Import(..) => return None,
            Target::Extern(s) => Name::new(s),
            Target::Def(_) => spelled,
        };
        let d = self.push_def(Definition {
            target: t,
            name,
            kind: SymbolKind::External,
            location: None,
            range: None,
            parent: None,
        });
        let at = externals.partition_point(|(x, _)| *x < t);
        externals.insert(at, (t, d));
        Some(d)
    }

    fn build_by_def(&mut self) {
        let n = self.defs.len();
        let mut count: Vec<u32> = alloc::vec![0; n + 1];
        for r in &self.refs {
            if let Some(c) = count.get_mut(r.def.index() + 1) {
                *c += 1;
            }
        }
        for i in 1..count.len() {
            let prev = count.get(i - 1).copied().unwrap_or(0);
            if let Some(c) = count.get_mut(i) {
                *c += prev;
            }
        }
        let mut fill = count.clone();
        let mut by_def: Vec<u32> = alloc::vec![0; self.refs.len()];
        // References are visited in location order so each slice is sorted.
        let mut order: Vec<u32> = (0..ix(self.refs.len())).collect();
        order.sort_by_key(|i| self.refs.get(*i as usize).map(|r| r.location));
        for i in order {
            let Some(r) = self.refs.get(i as usize) else {
                continue;
            };
            if let Some(f) = fill.get_mut(r.def.index()) {
                if let Some(slot) = by_def.get_mut(*f as usize) {
                    *slot = i;
                }
                *f += 1;
            }
        }
        self.by_def_off = count;
        self.by_def = by_def;
    }

    fn build_occurrences(&mut self) {
        let mut per_unit: Vec<Vec<(u32, u32, u32, u32)>> =
            self.units.iter().map(|_| Vec::new()).collect();
        let unit_pos = |units: &[UnitIx], id: UnitId| units.iter().position(|u| u.id == id);
        for (d, def) in self.defs.iter().enumerate() {
            let Some(loc) = def.location.filter(|l| l.in_source && !l.span.is_empty()) else {
                continue;
            };
            if let Some(list) = unit_pos(&self.units, loc.unit).and_then(|u| per_unit.get_mut(u)) {
                list.push((
                    loc.span.start().to_u32(),
                    loc.span.end().to_u32(),
                    ix(d),
                    NONE,
                ));
            }
        }
        for (i, r) in self.refs.iter().enumerate() {
            let loc = r.location;
            if !loc.in_source || loc.span.is_empty() {
                continue;
            }
            if let Some(list) = unit_pos(&self.units, loc.unit).and_then(|u| per_unit.get_mut(u)) {
                list.push((
                    loc.span.start().to_u32(),
                    loc.span.end().to_u32(),
                    r.def.0,
                    ix(i),
                ));
            }
        }
        for (u, mut list) in self.units.iter_mut().zip(per_unit) {
            list.sort_unstable();
            list.dedup_by_key(|x| (x.0, x.1));
            u.occ = list;
        }
    }

    // ----------------------------------------------------------------- API

    /// Every definition, in unit order, then preorder (externals last).
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Index;
    ///
    /// assert!(Index::default().definitions().is_empty());
    /// ```
    #[must_use]
    pub fn definitions(&self) -> &[Definition] {
        &self.defs
    }

    /// Every reference, by unit, then path, then segment.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Index;
    ///
    /// assert!(Index::default().references_all().is_empty());
    /// ```
    #[must_use]
    pub fn references_all(&self) -> &[Reference] {
        &self.refs
    }

    /// One definition.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{DefRef, Index};
    ///
    /// assert!(Index::default().definition(DefRef::from_index(0)).is_none());
    /// ```
    #[must_use]
    pub fn definition(&self, def: DefRef) -> Option<&Definition> {
        self.defs.get(def.index())
    }

    /// The references to a definition, sorted by location (find-references).
    /// Allocation-free: an iterator over the definition's slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{DefRef, Index};
    ///
    /// assert_eq!(Index::default().references(DefRef::from_index(0)).len(), 0);
    /// ```
    #[must_use]
    pub fn references(&self, def: DefRef) -> References<'_> {
        let ids = match (
            self.by_def_off.get(def.index()),
            self.by_def_off.get(def.index() + 1),
        ) {
            (Some(&lo), Some(&hi)) => self.by_def.get(lo as usize..hi as usize).unwrap_or(&[]),
            _ => &[],
        };
        References {
            refs: &self.refs,
            ids: ids.iter(),
        }
    }

    /// The definition of a target (an item, variant, binder, aliased import,
    /// or a referenced external symbol).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{BinderId, UnitId};
    /// use resolve_lang::{Index, Target};
    ///
    /// let t = Target::Local(UnitId::new(0), BinderId::from_index(0).unwrap());
    /// assert!(Index::default().def_of(t).is_none());
    /// ```
    #[must_use]
    pub fn def_of(&self, target: Target) -> Option<DefRef> {
        self.find_target(target, &self.externals)
    }

    /// Go-to-definition by HIR id: what segment `segment` of `path` names.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{PathId, UnitId};
    /// use resolve_lang::Index;
    ///
    /// assert!(Index::default().resolve_at(UnitId::new(0), PathId::from_index(0).unwrap(), 0).is_none());
    /// ```
    #[must_use]
    pub fn resolve_at(&self, unit: UnitId, path: PathId, segment: u32) -> Option<DefRef> {
        let u = self.unit_ix(unit)?;
        let lo = *u.path_off.get(path.index())? as usize;
        let hi = *u.path_off.get(path.index() + 1)? as usize;
        self.refs
            .get(lo..hi)?
            .iter()
            .find(|r| r.segment == segment)
            .map(|r| r.def)
    }

    /// The references inside one path, by segment.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{PathId, UnitId};
    /// use resolve_lang::Index;
    ///
    /// assert!(Index::default().path_references(UnitId::new(0), PathId::from_index(0).unwrap()).is_empty());
    /// ```
    #[must_use]
    pub fn path_references(&self, unit: UnitId, path: PathId) -> &[Reference] {
        let Some(u) = self.unit_ix(unit) else {
            return &[];
        };
        let (Some(&lo), Some(&hi)) = (
            u.path_off.get(path.index()),
            u.path_off.get(path.index() + 1),
        ) else {
            return &[];
        };
        self.refs.get(lo as usize..hi as usize).unwrap_or(&[])
    }

    /// Go-to-definition by position: the definition or reference whose name
    /// contains byte `offset` of `unit`'s source.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::UnitId;
    /// use resolve_lang::Index;
    ///
    /// assert!(Index::default().at(UnitId::new(0), 3).is_none());
    /// ```
    #[must_use]
    pub fn at(&self, unit: UnitId, offset: u32) -> Option<Occurrence> {
        let u = self.unit_ix(unit)?;
        let upper = u.occ.partition_point(|(s, _, _, _)| *s <= offset);
        // Names do not overlap in practice; look back a few entries for
        // the innermost one that contains the offset.
        let lo = upper.saturating_sub(8);
        u.occ
            .get(lo..upper)?
            .iter()
            .rev()
            .find(|(s, e, _, _)| *s <= offset && offset < *e)
            .map(|&(_, _, d, r)| Occurrence {
                def: DefRef(d),
                reference: (r != NONE).then_some(r),
            })
    }

    /// Every edit renaming a definition implies: its own name and every
    /// reference that spells the same name (references through an aliased
    /// import spell the alias and are left alone). Renaming an aliased
    /// import edits the alias and the references that went through it.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::{DefRef, Index};
    ///
    /// assert!(Index::default().rename_set(DefRef::from_index(0)).edits.is_empty());
    /// ```
    #[must_use]
    pub fn rename_set(&self, def: DefRef) -> RenameSet {
        let mut set = RenameSet::default();
        let Some(d) = self.definition(def) else {
            return set;
        };
        let mut add = |loc: Location| {
            if loc.in_source {
                set.edits.push(loc);
            } else {
                set.outside_source.push(loc);
            }
        };
        if let Some(loc) = d.location {
            add(loc);
        }
        if let Target::Import(..) = d.target {
            // The alias's references point at the import's target; take the
            // ones that went through this import.
            let lo = self.by_via.partition_point(|(v, _)| *v < def.0);
            for &(v, r) in self.by_via.get(lo..).unwrap_or(&[]) {
                if v != def.0 {
                    break;
                }
                if let Some(r) = self.refs.get(r as usize).filter(|r| r.name == d.name) {
                    add(r.location);
                }
            }
        } else {
            for r in self.references(def) {
                if r.name == d.name {
                    add(r.location);
                }
            }
        }
        set.edits.sort();
        set.edits.dedup();
        set.outside_source.sort();
        set.outside_source.dedup();
        set
    }

    /// The item definitions of a unit in preorder (with `parent` links), for
    /// a document outline.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::UnitId;
    /// use resolve_lang::Index;
    ///
    /// assert!(Index::default().document_symbols(UnitId::new(0)).is_empty());
    /// ```
    #[must_use]
    pub fn document_symbols(&self, unit: UnitId) -> Vec<(DefRef, &Definition)> {
        let Some(u) = self.unit_ix(unit) else {
            return Vec::new();
        };
        u.symbols
            .iter()
            .filter_map(|d| self.defs.get(*d as usize).map(|def| (DefRef(*d), def)))
            .collect()
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use hir_lang::{Builder, Expansion, ExpnKind, Name, Symbol};

    use super::*;

    #[test]
    fn test_mapper_maps_nested_expansions_to_outermost_call_site() {
        let mut b = Builder::new();
        let sym = Symbol::from_u32(1).unwrap();
        let outer = b.expansion(Expansion {
            kind: ExpnKind::Macro,
            name: sym,
            call_site: Span::new(100, 110),
            parent: ExpnId::ROOT,
            def_site: ExpnId::ROOT,
        });
        let inner = b.expansion(Expansion {
            kind: ExpnKind::Template,
            name: sym,
            call_site: Span::new(5, 6),
            parent: outer,
            def_site: ExpnId::ROOT,
        });
        let root = b.module(None, &[]);
        let hir = b.finish(root).unwrap();
        let map = Mapper::new(&hir);
        let loc = map.span(Span::new(1, 2), inner);
        assert_eq!(loc.span, Span::new(100, 110));
        assert!(!loc.in_source);
        let loc = map.span(Span::new(1, 2), ExpnId::ROOT);
        assert_eq!(loc.span, Span::new(1, 2));
        assert!(loc.in_source);
    }

    #[test]
    fn test_empty_index_answers_nothing() {
        let ix = Index::default();
        let d = DefRef::from_index(0);
        assert!(ix.definition(d).is_none());
        assert_eq!(ix.references(d).len(), 0);
        assert!(ix.rename_set(d).edits.is_empty());
        assert!(ix.at(UnitId::new(0), 0).is_none());
        let t = Target::Extern(Symbol::from_u32(1).unwrap());
        assert!(ix.def_of(t).is_none());
        let _ = Name::new(Symbol::from_u32(1).unwrap());
    }

    #[test]
    fn test_def_ref_saturates() {
        assert_eq!(DefRef::from_index(usize::MAX).index(), u32::MAX as usize);
    }
}
