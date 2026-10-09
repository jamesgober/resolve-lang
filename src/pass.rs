//! Phase 3: the resolving walk over one unit.
//!
//! The walk is hir-lang's own canonical traversal; this module only listens
//! to its events. Binders come from `Hir::lookup_local` (the HIR's scope
//! rule, never re-derived); item names come from per-name shadow stacks that
//! the walk pushes when a table scope opens (or when a declare-before-use
//! item is reached) and pops when the scope closes, so finding the innermost
//! visible item is O(1) per namespace. A binder and an item compete by
//! (scope depth, position): the innermost wins, and within one scope the one
//! that became visible last.
//!
//! Paths that need class member tables (`self::x`, `parent::x`,
//! `Class::member`) are planned partially here and finished after mixin
//! expansion (see `members`). So are unqualified names inside a class whose
//! members are lexically visible (`ClassScope::Lexical`) and that inherits:
//! an inherited member shadows a name of an enclosing scope, but inherited
//! members are only known once every base is resolved. Such a path is
//! resolved now as if nothing were inherited, the outcome is set aside, and
//! the member phase either replaces it with the inherited member or commits
//! it unchanged.
//!
//! Every table lookup goes through the table's key (`Fold::key`), so a
//! case-insensitive table finds a name in any ASCII case.

use alloc::{collections::BTreeMap, vec::Vec};

use hir_lang::{
    BinderId, BinderKind, Control, Event, Expr, ExprId, Frame, Hir, IdKind, ItemId, ItemKind, Name,
    NodeRef, Ns, Pat, PathId, PathRoot, Res, Span, Stmt,
};
use intern_lang::Lookup;

use crate::{
    diag::{DiagKind, Diagnostic},
    env::DefKind,
    imports::Hit,
    model::{ANY_NS, EntryState, ImportState, Model, NONE, Origin, ScopeKind, Unit, ix},
    policy::{ClassScope, Hoist, ItemClass, ModuleScope, Namespace, Shadowing, TABLES},
    suggest::{MAX_CANDIDATES, Suggester},
};

/// One resolved segment, for the index.
#[derive(Clone, Copy, Debug)]
pub(crate) struct SegRef {
    pub(crate) path: PathId,
    pub(crate) seg: u32,
    pub(crate) res: Res,
    /// The import the name was reached through (import index), or `NONE`.
    pub(crate) via: u32,
}

/// The type context a path sits in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TypeCtx {
    None,
    /// A class or interface (its member table scope).
    Type(u32),
    /// An impl block.
    Impl,
}

/// What still needs member tables.
#[derive(Clone, Copy, Debug)]
pub(crate) enum DeferKind {
    Root(PathRoot),
    /// Segment `seg` onward is a member of `container`.
    Member {
        seg: u32,
        container: Hit,
    },
    /// An unqualified name an inherited member may shadow; the index of the
    /// set-aside outcome in `UnitOut::fallbacks`.
    Lexical(u32),
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Deferred {
    pub(crate) path: PathId,
    pub(crate) kind: DeferKind,
    pub(crate) ctx: TypeCtx,
    /// The module scope the path is in (for module access checks).
    pub(crate) module: u32,
    /// Whether the path is the callee of a call (functions before constants).
    pub(crate) callee: bool,
}

/// The outcome of resolving a path as if nothing were inherited, set aside
/// until the member phase knows whether an inherited member shadows it.
#[derive(Clone, Debug, Default)]
pub(crate) struct Fallback {
    /// The classes (member-table scopes) whose inherited members are
    /// searched, innermost first.
    pub(crate) classes: Vec<u32>,
    /// The pattern, when the path is a bare identifier pattern's.
    pub(crate) pat: Option<hir_lang::PatId>,
    pub(crate) plan: Option<(Res, u32)>,
    pub(crate) diagnosed: bool,
    pub(crate) segs: Vec<SegRef>,
    pub(crate) diags: Vec<Diagnostic>,
    pub(crate) deferred: Vec<Deferred>,
    pub(crate) ident_matches: Vec<hir_lang::PatId>,
}

/// What phase 3 produced for one unit.
pub(crate) struct UnitOut {
    /// The planned resolution of each path: (res, unresolved).
    pub(crate) plan: Vec<Option<(Res, u32)>>,
    /// Paths that already have a diagnostic.
    pub(crate) diagnosed: Vec<bool>,
    pub(crate) segs: Vec<SegRef>,
    pub(crate) deferred: Vec<Deferred>,
    pub(crate) diags: Vec<Diagnostic>,
    /// `Pat::Ident` patterns whose path named a constant (they match, not bind).
    pub(crate) ident_matches: Vec<hir_lang::PatId>,
    /// Set-aside outcomes of `DeferKind::Lexical` paths.
    pub(crate) fallbacks: Vec<Fallback>,
}

impl UnitOut {
    pub(crate) fn plan(&mut self, path: PathId, res: Res, unresolved: u32) {
        if let Some(slot) = self.plan.get_mut(path.index()) {
            *slot = Some((res, unresolved));
        }
    }

    /// Records a diagnostic about `path` (at most one per path) and plans
    /// `Res::Err` unless `keep` (access errors keep their resolution).
    pub(crate) fn diag(
        &mut self,
        unit: hir_lang::UnitId,
        path: PathId,
        kind: DiagKind,
        span: Span,
        keep: bool,
    ) {
        let first = self
            .diagnosed
            .get_mut(path.index())
            .is_some_and(|d| !core::mem::replace(d, true));
        if !keep {
            // The path's segment references are dropped when the index is
            // built (it skips paths that end as `Res::Err`).
            self.plan(path, Res::Err, 0);
        }
        if first {
            self.diags.push(Diagnostic {
                kind,
                unit,
                span,
                node: Some(NodeRef::Path(path)),
            });
        }
    }
}

/// A visible table entry or a type-parameter binder on a shadow stack.
#[derive(Clone, Copy, Debug)]
enum Item {
    Table(u32, u32),
    Binder(BinderId),
}

#[derive(Clone, Copy, Debug)]
struct StackEntry {
    key: u32,
    prev: u32,
    prev_skip: u32,
    depth: u32,
    seq: u32,
    world: u32,
    /// `NONE`, or the frame index of the class whose body alone sees it.
    ctx: u32,
    item: Item,
}

struct ScopeRec {
    entries: u32,
    visible: u32,
    shadow: u32,
}

#[derive(Clone, Copy)]
enum FrameKind {
    /// An item frame; `init` for a constant or global (a class-body
    /// initializer in Python terms).
    Item {
        init: bool,
    },
    Other,
}

struct FrameRec {
    kind: FrameKind,
    prev_world: u32,
    module: bool,
    ctx: bool,
}

#[derive(Clone, Copy)]
enum Pending {
    None,
    Table(u32),
}

/// The best candidate found for a first segment.
#[derive(Clone, Copy)]
enum Cand {
    Binder(BinderId, bool),
    Entry(u32, u32),
}

/// A class scope whose members are lexically visible, open on the walk.
#[derive(Clone, Copy)]
struct LexClass {
    table: u32,
    /// The walk depth of its table scope (its own members' depth).
    depth: u32,
    world: u32,
    /// Whether it has bases or mixins (members not on the shadow stacks).
    inherits: bool,
    /// Whether the walk is past the class header (generics, bases,
    /// interfaces) and into its fields and members. The header never sees
    /// the class's inherited members: the bases are what it names.
    in_body: bool,
}

/// What a path's context makes of it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Ctx {
    Normal,
    Import(u32),
    GlobalDecl,
    PatIdent(hir_lang::PatId),
}

pub(crate) struct Pass<'p, 'e, L> {
    m: &'p Model<'e>,
    names: &'p L,
    sugg: &'p mut Suggester,
    unit: &'p Unit,
    hir: &'p Hir,
    keys: Vec<Name>,
    heads: Vec<u32>,
    entries: Vec<StackEntry>,
    seq: u32,
    depth: u32,
    scopes: Vec<ScopeRec>,
    tables: Vec<u32>,
    /// The open table scopes only (for suggestions).
    open_tables: Vec<u32>,
    /// Environment root and prelude names, collected on first need.
    env_names: Option<Vec<Name>>,
    frames: Vec<FrameRec>,
    world: u32,
    type_ctx: Vec<TypeCtx>,
    modules: Vec<u32>,
    binder_info: Vec<(u32, u32)>,
    visible: Vec<BinderId>,
    shadow: BTreeMap<Name, Vec<(BinderId, u32, u32)>>,
    shadow_log: Vec<Name>,
    pending: Pending,
    hint: Option<NodeRef>,
    /// By expression index: whether it is the callee of a call. Empty when
    /// the policy keeps constants in the value table (no difference then).
    callees: Vec<bool>,
    lex_classes: Vec<LexClass>,
    /// Fully folded names of every class member of the program (built only
    /// under `ClassScope::Lexical`), sorted: a set-aside name that is one of
    /// them is likely inherited, so its outcome skips did-you-mean.
    member_names: Vec<Name>,
    /// Suggestions are off while resolving such a name.
    quiet: bool,
    pub(crate) out: UnitOut,
}

impl<'p, 'e, L: Lookup> Pass<'p, 'e, L> {
    pub(crate) fn new(
        m: &'p Model<'e>,
        names: &'p L,
        sugg: &'p mut Suggester,
        u: u32,
    ) -> Option<Self> {
        let unit = m.units.get(u as usize)?;
        let hir = &unit.hir;
        let n_paths = hir.count(IdKind::Path);
        // Only names some path starts with can be looked up lexically: the
        // shadow stacks are keyed by those names alone.
        // Under case folding a name is looked up by its key in each table,
        // which is the name itself or its folded form; both are keys here.
        let mut keys: Vec<Name> = Vec::with_capacity(n_paths);
        for i in 0..n_paths {
            let Some(p) = PathId::from_index(i).and_then(|p| hir.get_path(p)) else {
                continue;
            };
            if let Some(seg) = hir.list(p.segments).first() {
                keys.push(seg.name);
                let folded = m.fold.name(seg.name);
                if folded != seg.name {
                    keys.push(folded);
                }
            }
        }
        keys.sort();
        keys.dedup();
        let split = m.policy.table_ix(Namespace::Const) != m.policy.table_ix(Namespace::Value);
        let mut callees = Vec::new();
        if split {
            let n = hir.count(IdKind::Expr);
            callees = alloc::vec![false; n];
            for i in 0..n {
                let Some(e) = ExprId::from_index(i) else {
                    continue;
                };
                if let Some(Expr::Call { callee, .. }) = hir.get_expr(e) {
                    if let Some(slot) = callees.get_mut(callee.index()) {
                        *slot = true;
                    }
                }
            }
        }
        let heads = alloc::vec![NONE; keys.len().saturating_mul(TABLES)];
        let mut member_names: Vec<Name> = Vec::new();
        if m.policy.class_scope() == ClassScope::Lexical {
            for scope in &m.scopes {
                if matches!(scope.kind, ScopeKind::Type(..)) {
                    member_names.extend(
                        scope
                            .defs
                            .iter()
                            .filter_map(|b| m.bindings.get(*b as usize))
                            .map(|b| m.fold.name(b.name)),
                    );
                }
            }
            member_names.sort();
            member_names.dedup();
        }
        Some(Self {
            m,
            names,
            sugg,
            unit,
            hir,
            keys,
            heads,
            entries: Vec::new(),
            seq: 0,
            depth: 0,
            scopes: Vec::new(),
            tables: Vec::new(),
            open_tables: Vec::new(),
            env_names: None,
            frames: Vec::new(),
            world: 0,
            type_ctx: Vec::new(),
            modules: Vec::new(),
            binder_info: alloc::vec![(0, NONE); hir.count(IdKind::Binder)],
            visible: Vec::new(),
            shadow: BTreeMap::new(),
            shadow_log: Vec::new(),
            pending: Pending::None,
            hint: None,
            callees,
            lex_classes: Vec::new(),
            member_names,
            quiet: false,
            out: UnitOut {
                plan: alloc::vec![None; n_paths],
                diagnosed: alloc::vec![false; n_paths],
                segs: Vec::new(),
                deferred: Vec::new(),
                diags: Vec::new(),
                ident_matches: Vec::new(),
                fallbacks: Vec::new(),
            },
        })
    }

    pub(crate) fn run(mut self) -> UnitOut {
        let hir = self.hir;
        hir.walk_from(NodeRef::Item(hir.root()), |ev| {
            self.event(ev);
            Control::Continue
        });
        self.out
    }

    fn unit_id(&self) -> hir_lang::UnitId {
        self.unit.id
    }

    fn module(&self) -> u32 {
        self.modules.last().copied().unwrap_or(self.unit.root_scope)
    }

    // ------------------------------------------------------------- events

    fn event(&mut self, ev: Event) {
        self.seq = self.seq.saturating_add(1);
        match ev {
            Event::Enter(node) => {
                self.pending = Pending::None;
                match node {
                    NodeRef::Path(p) => self.path(p),
                    NodeRef::Item(i) => {
                        // A mixin use names what the class inherits, like
                        // its bases: it is header, not body.
                        let mixin = matches!(self.hir.item(i).kind, ItemKind::MixinUse(_));
                        self.enter_member(!mixin);
                        self.push_gated(i);
                        self.hint = Some(node);
                    }
                    NodeRef::Field(_) => {
                        self.enter_member(true);
                        self.hint = Some(node);
                    }
                    NodeRef::Expr(e) => {
                        let t = self
                            .unit
                            .block_scope
                            .get(e.index())
                            .copied()
                            .unwrap_or(NONE);
                        if t != NONE {
                            self.pending = Pending::Table(t);
                        }
                        self.hint = Some(node);
                    }
                    _ => self.hint = Some(node),
                }
            }
            Event::FrameOpen(frame) => self.frame_open(frame),
            Event::FrameClose => self.frame_close(),
            Event::ScopeOpen => self.scope_open(),
            Event::ScopeClose => self.scope_close(),
            Event::Bind(b) => self.bind(b),
            _ => self.pending = Pending::None,
        }
    }

    /// A field or item is entered: if it is a direct member of the
    /// innermost lexical class, the walk is in that class's body (`body`)
    /// or in a part that names what it inherits (a mixin use).
    fn enter_member(&mut self, body: bool) {
        let here = self.tables.last().copied();
        if let Some(c) = self.lex_classes.last_mut() {
            if here == Some(c.table) {
                c.in_body = body;
            }
        }
    }

    fn frame_open(&mut self, frame: Frame) {
        self.pending = Pending::None;
        let mut rec = FrameRec {
            kind: FrameKind::Other,
            prev_world: self.world,
            module: false,
            ctx: false,
        };
        if let Frame::Item(i) = frame {
            let kind = &self.hir.item(i).kind;
            rec.kind = FrameKind::Item {
                init: matches!(kind, ItemKind::Const { .. } | ItemKind::Global { .. }),
            };
            let table = self.unit.item_scope.get(i.index()).copied().unwrap_or(NONE);
            match kind {
                ItemKind::Module { .. } => {
                    if table != NONE {
                        self.modules.push(table);
                        rec.module = true;
                        if self.m.policy.module_scope() == ModuleScope::Isolated {
                            self.world = table.saturating_add(1);
                        }
                    }
                    self.pending = Pending::Table(table);
                }
                ItemKind::Class(_) | ItemKind::Interface(_) => {
                    self.type_ctx.push(if table == NONE {
                        TypeCtx::Impl
                    } else {
                        TypeCtx::Type(table)
                    });
                    rec.ctx = true;
                    self.pending = Pending::Table(table);
                }
                ItemKind::Impl(_) => {
                    self.type_ctx.push(TypeCtx::Impl);
                    rec.ctx = true;
                }
                _ => {}
            }
        }
        self.frames.push(rec);
    }

    fn frame_close(&mut self) {
        self.pending = Pending::None;
        let Some(rec) = self.frames.pop() else { return };
        self.world = rec.prev_world;
        if rec.module {
            let _ = self.modules.pop();
        }
        if rec.ctx {
            let _ = self.type_ctx.pop();
        }
    }

    fn scope_open(&mut self) {
        self.depth += 1;
        self.scopes.push(ScopeRec {
            entries: ix(self.entries.len()),
            visible: ix(self.visible.len()),
            shadow: ix(self.shadow_log.len()),
        });
        let table = match core::mem::replace(&mut self.pending, Pending::None) {
            Pending::Table(t) if t != NONE => t,
            _ => {
                self.tables.push(NONE);
                return;
            }
        };
        self.tables.push(table);
        self.open_tables.push(table);
        let Some(ctx) = self.table_ctx(table) else {
            return;
        };
        let Some(scope) = self.m.scopes.get(table as usize) else {
            return;
        };
        for (e, entry) in scope.table.iter().enumerate() {
            if entry_gate(self.m, entry.state).is_some() {
                continue;
            }
            self.push_entry(*entry, ctx, Item::Table(table, ix(e)));
        }
        if let ScopeKind::Type(item, true) = scope.kind {
            if self.m.policy.class_scope() == ClassScope::Lexical {
                let has_bases = match &self.hir.item(item).kind {
                    ItemKind::Class(c) => !c.bases.is_empty(),
                    _ => false,
                };
                self.lex_classes.push(LexClass {
                    table,
                    depth: self.depth,
                    world: self.world,
                    inherits: has_bases || !scope.mixin_uses.is_empty(),
                    in_body: false,
                });
            }
        }
    }

    /// How a table's entries are seen from inside: `None` if not lexically
    /// at all (interfaces, qualified-only class bodies), else the context
    /// tag of its stack entries (`NONE` = everywhere in the scope, or the
    /// class frame whose body alone sees them).
    fn table_ctx(&self, table: u32) -> Option<u32> {
        let scope = self.m.scopes.get(table as usize)?;
        match scope.kind {
            ScopeKind::Type(_, false) => None,
            ScopeKind::Type(_, true) => match self.m.policy.class_scope() {
                ClassScope::Qualified => None,
                ClassScope::Lexical => Some(NONE),
                ClassScope::BodyOnly => Some(ix(self.frames.len().saturating_sub(1))),
            },
            _ => Some(NONE),
        }
    }

    fn scope_close(&mut self) {
        self.pending = Pending::None;
        if let Some(t) = self.tables.pop() {
            if t != NONE {
                let _ = self.open_tables.pop();
                if self.lex_classes.last().is_some_and(|c| c.table == t) {
                    let _ = self.lex_classes.pop();
                }
            }
        }
        let Some(rec) = self.scopes.pop() else { return };
        self.depth = self.depth.saturating_sub(1);
        while self.entries.len() > rec.entries as usize {
            let Some(e) = self.entries.pop() else { break };
            if let Some(h) = self.heads.get_mut(e.key as usize) {
                *h = e.prev;
            }
        }
        self.visible.truncate(rec.visible as usize);
        while self.shadow_log.len() > rec.shadow as usize {
            let Some(name) = self.shadow_log.pop() else {
                break;
            };
            if let Some(stack) = self.shadow.get_mut(&name) {
                let _ = stack.pop();
                if stack.is_empty() {
                    let _ = self.shadow.remove(&name);
                }
            }
        }
    }

    fn bind(&mut self, b: BinderId) {
        if let Some(slot) = self.binder_info.get_mut(b.index()) {
            *slot = (self.depth, self.seq);
        }
        self.visible.push(b);
        let Some(binder) = self.hir.binder(b).copied() else {
            return;
        };
        if binder.kind == BinderKind::TypeParam {
            let t = self.m.policy.table_ix(Namespace::Type);
            let key = self.m.fold.key(t, binder.name);
            self.push_key(t, key, NONE, Item::Binder(b));
        }
        let policy = self.m.policy.shadowing();
        if policy == Shadowing::Allow || !binder.kind.is_value() {
            return;
        }
        let frame = ix(self.frames.len());
        if let Some(&(prev, depth, prev_frame)) =
            self.shadow.get(&binder.name).and_then(|s| s.last())
        {
            let bad = match policy {
                Shadowing::DenySameScope => depth == self.depth,
                Shadowing::DenyLocals => prev_frame == frame,
                Shadowing::Allow => false,
            };
            if bad {
                self.out.diags.push(Diagnostic {
                    kind: DiagKind::Shadowing {
                        name: binder.name,
                        shadowed: prev,
                    },
                    unit: self.unit.id,
                    span: self.hir.binder_origin(b).span,
                    node: None,
                });
            }
        }
        self.shadow
            .entry(binder.name)
            .or_default()
            .push((b, self.depth, frame));
        self.shadow_log.push(binder.name);
    }

    /// Pushes the entries a declare-before-use item makes visible.
    fn push_gated(&mut self, item: ItemId) {
        let list = &self.unit.after_decl;
        let key = ix(item.index());
        let lo = list.partition_point(|(i, _, _)| *i < key);
        let hi = list.partition_point(|(i, _, _)| *i <= key);
        for &(_, scope, entry) in list.get(lo..hi).unwrap_or(&[]) {
            let Some(e) = self
                .m
                .scopes
                .get(scope as usize)
                .and_then(|s| s.table.get(entry as usize))
                .copied()
            else {
                continue;
            };
            // Only entries of a scope that is open now (the declaring one).
            if self.tables.last().copied() != Some(scope) {
                continue;
            }
            let Some(ctx) = self.table_ctx(scope) else {
                continue;
            };
            self.push_entry(e, ctx, Item::Table(scope, entry));
        }
    }

    fn push_entry(&mut self, entry: crate::model::Entry, ctx: u32, item: Item) {
        if entry.ns == ANY_NS {
            for t in 0..TABLES as u8 {
                let key = self.m.fold.key(t, entry.spelling);
                self.push_key(t, key, ctx, item);
            }
        } else {
            self.push_key(entry.ns, entry.name, ctx, item);
        }
    }

    /// Pushes `item` on the shadow stack of `name` (already a key of table
    /// `t`) in table `t`.
    fn push_key(&mut self, t: u8, name: Name, ctx: u32, item: Item) {
        let Ok(k) = self.keys.binary_search(&name) else {
            return;
        };
        let key = ix(k * TABLES + t as usize);
        let Some(&prev) = self.heads.get(key as usize) else {
            return;
        };
        let prev_skip = match self.entries.get(prev as usize) {
            Some(p) if p.ctx != NONE => p.prev_skip,
            _ => prev,
        };
        let e = StackEntry {
            key,
            prev,
            prev_skip,
            depth: self.depth,
            seq: self.seq,
            world: self.world,
            ctx,
            item,
        };
        if let Some(h) = self.heads.get_mut(key as usize) {
            *h = ix(self.entries.len());
        }
        self.entries.push(e);
    }

    /// The innermost visible entry for `name` in table `t`.
    fn top(&self, t: u8, name: Name) -> Option<StackEntry> {
        let key = self.m.fold.key(t, name);
        let k = self.keys.binary_search(&key).ok()?;
        let mut at = *self.heads.get(k * TABLES + t as usize)?;
        for _ in 0..3 {
            let e = *self.entries.get(at as usize)?;
            if e.world != self.world {
                return None;
            }
            if e.ctx == NONE || self.class_body_visible(e.ctx) {
                return Some(e);
            }
            at = e.prev_skip;
        }
        None
    }

    /// Whether the body of the class whose frame is `f` is visible here:
    /// directly in the class, or in a constant/global initializer of it.
    fn class_body_visible(&self, f: u32) -> bool {
        let top = self.frames.len().saturating_sub(1);
        let f = f as usize;
        top == f
            || (top == f + 1
                && matches!(
                    self.frames.get(top).map(|r| r.kind),
                    Some(FrameKind::Item { init: true })
                ))
    }

    // -------------------------------------------------------------- paths

    fn ctx_of(&self, p: PathId) -> Ctx {
        match self.hint {
            Some(NodeRef::Item(i)) => match self.hir.item(i).kind {
                ItemKind::Import { path, .. } if path == p => {
                    let imp = self.unit.import_of.get(i.index()).copied().unwrap_or(NONE);
                    Ctx::Import(imp)
                }
                _ => Ctx::Normal,
            },
            Some(NodeRef::Stmt(s)) => match *self.hir.stmt(s) {
                Stmt::Global { path, .. } if path == p => Ctx::GlobalDecl,
                _ => Ctx::Normal,
            },
            Some(NodeRef::Pat(pat)) => match *self.hir.pat(pat) {
                Pat::Ident { path, .. } if path == p => Ctx::PatIdent(pat),
                _ => Ctx::Normal,
            },
            _ => Ctx::Normal,
        }
    }

    fn seg_span(&self, p: PathId, seg: usize) -> Span {
        let path = self.hir.path(p);
        self.hir
            .list(path.segments)
            .get(seg)
            .map_or(self.hir.origin(NodeRef::Path(p)).span, |s| s.origin.span)
    }

    fn diag(&mut self, p: PathId, kind: DiagKind, seg: usize, keep: bool) {
        let span = self.seg_span(p, seg);
        let unit = self.unit_id();
        self.out.diag(unit, p, kind, span, keep);
    }

    fn seg_ref(&mut self, p: PathId, seg: usize, res: Res, binding: u32) {
        let via = self
            .m
            .bindings
            .get(binding as usize)
            .map_or(NONE, |b| match b.origin {
                Origin::Import(i) | Origin::Glob(i, _) | Origin::Variant(i, _) => i,
                _ => NONE,
            });
        self.out.segs.push(SegRef {
            path: p,
            seg: ix(seg),
            res,
            via,
        });
    }

    fn path(&mut self, p: PathId) {
        let path = *self.hir.path(p);
        let ctx = self.ctx_of(p);
        if let Ctx::Import(i) = ctx {
            self.import_path(p, i);
            return;
        }
        let n = path.segments.len();
        if n == 0 {
            return;
        }
        if !path.res.is_unresolved() {
            // Already resolved by lowering (template temporaries, use_binder).
            let seg = n.saturating_sub(path.unresolved as usize).saturating_sub(1);
            if path.res != Res::Err {
                self.seg_ref(p, seg, path.res, NONE);
            }
            return;
        }
        if path.root.is_type_root() {
            let ctx = self.type_ctx.last().copied().unwrap_or(TypeCtx::None);
            let callee = self.is_callee(p);
            self.out.deferred.push(Deferred {
                path: p,
                kind: DeferKind::Root(path.root),
                ctx,
                module: self.module(),
                callee,
            });
            return;
        }
        // A qualified self: only the trait's segments are ours.
        let (count, rest) = match path.qself {
            Some(q) => {
                let k = (q.trait_len as usize).min(n);
                if k == 0 {
                    self.out.plan(p, Res::Unresolved, ix(n));
                    return;
                }
                (k, n - k)
            }
            None => (n, 0),
        };
        self.resolve(p, ctx, count, rest);
    }

    fn import_path(&mut self, p: PathId, i: u32) {
        let Some(imp) = self.m.imports.get(i as usize) else {
            return;
        };
        match imp.state {
            ImportState::Done => {
                self.out.plan(p, imp.res, imp.unresolved);
                for &(seg, res, b) in &imp.segs {
                    self.seg_ref(p, seg as usize, res, b);
                }
            }
            // The import's diagnostic was reported when it failed.
            ImportState::Failed | ImportState::Pending => {
                self.out.plan(p, Res::Err, 0);
                if let Some(d) = self.out.diagnosed.get_mut(p.index()) {
                    *d = true;
                }
            }
        }
    }

    /// Whether path `p` is the callee of a call (only tracked when the
    /// policy keeps constants apart from functions).
    fn is_callee(&self, p: PathId) -> bool {
        match self.hint {
            Some(NodeRef::Expr(e)) => {
                self.callees.get(e.index()).copied().unwrap_or(false)
                    && matches!(self.hir.get_expr(e), Some(Expr::Path(q)) if *q == p)
            }
            _ => false,
        }
    }

    /// The table indexes a segment searches.
    fn tables_for(&self, ns: Ns, prefix: bool, callee: bool) -> Vec<u8> {
        tables_for(&self.m.policy, ns, prefix, callee)
    }

    fn hit_of_binding(&self, b: u32) -> Option<Hit> {
        self.m.bindings.get(b as usize).map(|x| Hit {
            res: x.res,
            kind: x.kind,
            vis: x.vis,
            binding: b,
        })
    }

    /// Resolves the first `count` segments of `p` (the rest, `rest`, are
    /// left type-directed). An unqualified name that an inherited member
    /// may shadow is resolved and set aside for the member phase.
    fn resolve(&mut self, p: PathId, ctx: Ctx, count: usize, rest: usize) {
        let path = *self.hir.path(p);
        let shadowable = path.root == PathRoot::Relative
            && path.qself.is_none()
            && matches!(ctx, Ctx::Normal | Ctx::PatIdent(_))
            && !self.lex_classes.is_empty();
        if shadowable {
            if let Some(first) = self.hir.list(path.segments).first().copied() {
                let classes = self.inheriting_classes(p, first.name, count > 1 || rest > 0);
                if !classes.is_empty() {
                    self.set_aside(p, ctx, count, rest, classes);
                    return;
                }
            }
        }
        self.resolve_now(p, ctx, count, rest);
    }

    /// The lexically visible classes, innermost first, whose inherited
    /// members could shadow the best lexical candidate for `name`: those
    /// that inherit and enclose that candidate's scope.
    fn inheriting_classes(&self, p: PathId, name: Name, prefix: bool) -> Vec<u32> {
        let ns = self.hir.path(p).ns;
        let callee = self.is_callee(p);
        let mut best: Option<u32> = None;
        if ns != Ns::Import {
            if let Some(b) = self.hir.lookup_local(p, name) {
                let (depth, seq) = self
                    .binder_info
                    .get(b.index())
                    .copied()
                    .unwrap_or((0, NONE));
                if seq != NONE {
                    best = Some(depth);
                }
            }
        }
        for t in self.tables_for(ns, prefix, callee) {
            if let Some(e) = self.top(t, name) {
                best = Some(best.map_or(e.depth, |d| d.max(e.depth)));
            }
        }
        let mut out = Vec::new();
        for c in self.lex_classes.iter().rev() {
            if c.world != self.world || best.is_some_and(|d| d >= c.depth) {
                break;
            }
            if c.inherits && c.in_body {
                out.push(c.table);
            }
        }
        out
    }

    /// Resolves `p` as if nothing were inherited, then sets the outcome
    /// aside (restoring `out`) behind a `DeferKind::Lexical` deferral.
    fn set_aside(&mut self, p: PathId, ctx: Ctx, count: usize, rest: usize, classes: Vec<u32>) {
        let i = p.index();
        let plan0 = self.out.plan.get(i).copied().flatten();
        let diagnosed0 = self.out.diagnosed.get(i).copied().unwrap_or(false);
        let (segs0, diags0, deferred0, idents0) = (
            self.out.segs.len(),
            self.out.diags.len(),
            self.out.deferred.len(),
            self.out.ident_matches.len(),
        );
        // A name some class defines is most likely an inherited member, and
        // then this outcome is discarded: do not pay for a suggestion that
        // will not be shown. A genuine typo is rarely a member name anywhere,
        // so it keeps its suggestion.
        let first = self
            .hir
            .list(self.hir.path(p).segments)
            .first()
            .map(|s| s.name);
        self.quiet = first.is_some_and(|n| {
            self.member_names
                .binary_search(&self.m.fold.name(n))
                .is_ok()
        });
        self.resolve_now(p, ctx, count, rest);
        self.quiet = false;
        let fallback = Fallback {
            classes,
            pat: match ctx {
                Ctx::PatIdent(pat) => Some(pat),
                _ => None,
            },
            plan: self.out.plan.get(i).copied().flatten(),
            diagnosed: self.out.diagnosed.get(i).copied().unwrap_or(false),
            segs: self.out.segs.split_off(segs0),
            diags: self.out.diags.split_off(diags0),
            deferred: self.out.deferred.split_off(deferred0),
            ident_matches: self.out.ident_matches.split_off(idents0),
        };
        if let Some(slot) = self.out.plan.get_mut(i) {
            *slot = plan0;
        }
        if let Some(slot) = self.out.diagnosed.get_mut(i) {
            *slot = diagnosed0;
        }
        let f = ix(self.out.fallbacks.len());
        self.out.fallbacks.push(fallback);
        let ctx_t = self.type_ctx.last().copied().unwrap_or(TypeCtx::None);
        let callee = self.is_callee(p);
        self.out.deferred.push(Deferred {
            path: p,
            kind: DeferKind::Lexical(f),
            ctx: ctx_t,
            module: self.module(),
            callee,
        });
    }

    fn resolve_now(&mut self, p: PathId, ctx: Ctx, count: usize, rest: usize) {
        let path = *self.hir.path(p);
        let segs = self.hir.list(path.segments);
        let Some(first) = segs.first().copied() else {
            return;
        };
        let prefix = count > 1 || rest > 0;
        let ns = path.ns;
        let start = match path.root {
            PathRoot::Relative => match ctx {
                Ctx::GlobalDecl => self.global_decl(p, first.name),
                _ => self.first(p, ctx, first.name, prefix),
            },
            PathRoot::Global => {
                let root = self.unit.root_scope;
                self.in_table(p, root, first.name, ns, prefix, 0)
                    .or_else(|| self.root_hit(first.name).map(Start::Hit))
                    .unwrap_or(Start::Unresolved)
            }
            PathRoot::SelfModule | PathRoot::Super(_) => {
                let levels = match path.root {
                    PathRoot::Super(k) => k,
                    _ => 0,
                };
                match self.ancestor(levels) {
                    Some(s) => self
                        .in_table(p, s, first.name, ns, prefix, 0)
                        .unwrap_or(Start::Unresolved),
                    None => {
                        self.diag(p, DiagKind::SuperBeyondRoot { levels }, 0, false);
                        return;
                    }
                }
            }
            _ => return,
        };
        let mut cur = match start {
            Start::Hit(h) => h,
            Start::Done => return,
            Start::Bind => return,
            Start::Unresolved => {
                if let Ctx::PatIdent(_) = ctx {
                    // An unknown bare identifier in a pattern binds.
                    return;
                }
                // Found in another namespace: say what it is instead.
                if let (PathRoot::Relative, false) = (path.root, prefix) {
                    if let Some(found) = self.probe_other(first.name, ns) {
                        self.diag(
                            p,
                            DiagKind::WrongKind {
                                name: first.name,
                                ns,
                                found,
                            },
                            0,
                            false,
                        );
                        return;
                    }
                }
                let suggestion = self.suggest_first(p, first.name, ns);
                self.diag(
                    p,
                    DiagKind::Unresolved {
                        name: first.name,
                        ns,
                        container: None,
                        suggestion,
                    },
                    0,
                    false,
                );
                return;
            }
        };
        self.walk_segments(p, ctx, &mut cur, 1, count, rest);
    }

    /// Continues a path from segment `k` with `cur` resolved so far.
    fn walk_segments(
        &mut self,
        p: PathId,
        ctx: Ctx,
        cur: &mut Hit,
        from: usize,
        count: usize,
        rest: usize,
    ) {
        let path = *self.hir.path(p);
        let segs = self.hir.list(path.segments);
        let n = segs.len();
        let ns = path.ns;
        let callee = self.is_callee(p);
        let mut prev_name = segs.get(from.saturating_sub(1)).map(|s| s.name);
        for k in from..count {
            let Some(seg) = segs.get(k).copied() else {
                break;
            };
            let last = k + 1 == count && rest == 0;
            let container_name = prev_name.unwrap_or(seg.name);
            let ts = self.tables_for(ns, !last, callee);
            // A program module: its table.
            if cur.kind == DefKind::Module {
                if let Some(s) = self.m.scope_of(cur.res) {
                    match self.in_table(p, s, seg.name, ns, !last, k) {
                        Some(Start::Hit(h)) => {
                            self.seg_ref(p, k - 1, cur.res, cur.binding);
                            *cur = h;
                            prev_name = Some(seg.name);
                            continue;
                        }
                        Some(_) => return,
                        None => {
                            let suggestion = self.suggest_in(s, seg.name);
                            self.diag(
                                p,
                                DiagKind::Unresolved {
                                    name: seg.name,
                                    ns,
                                    container: Some(container_name),
                                    suggestion,
                                },
                                k,
                                false,
                            );
                            return;
                        }
                    }
                }
            }
            // A program sum: its variants; anything else is type-directed.
            if let Some((u, t)) = self.m.sum_of(cur.res) {
                let table = self.m.sums.get(t as usize).map_or(&[][..], Vec::as_slice);
                let found = seg
                    .name
                    .mark
                    .is_root()
                    .then(|| table.binary_search_by(|(s, _)| s.cmp(&seg.name.sym)).ok())
                    .flatten()
                    .and_then(|i| table.get(i));
                match found {
                    Some(&(_, v)) if last => {
                        let unit_variant = self
                            .m
                            .units
                            .get(u as usize)
                            .and_then(|unit| unit.hir.variant(v))
                            .is_some_and(|v| v.shape == hir_lang::Shape::Unit);
                        self.seg_ref(p, k - 1, cur.res, cur.binding);
                        *cur = Hit {
                            res: Res::Def(self.m.def_id(u, hir_lang::Def::Variant(v))),
                            kind: DefKind::Variant { unit: unit_variant },
                            vis: cur.vis,
                            binding: NONE,
                        };
                        prev_name = Some(seg.name);
                        continue;
                    }
                    Some(_) => {
                        self.diag(
                            p,
                            DiagKind::NotAContainer {
                                name: seg.name,
                                found: DefKind::Variant { unit: false },
                            },
                            k,
                            false,
                        );
                        return;
                    }
                    None => {
                        self.partial(p, *cur, n - k);
                        return;
                    }
                }
            }
            // A program class or interface: members after mixin expansion.
            if matches!(cur.kind, DefKind::Class { .. } | DefKind::Interface)
                && self.m.scope_of(cur.res).is_some()
            {
                let ctx_t = self.type_ctx.last().copied().unwrap_or(TypeCtx::None);
                self.seg_ref(p, k - 1, cur.res, cur.binding);
                self.out.plan(p, cur.res, ix(n - k));
                self.out.deferred.push(Deferred {
                    path: p,
                    kind: DeferKind::Member {
                        seg: ix(k),
                        container: *cur,
                    },
                    ctx: ctx_t,
                    module: self.module(),
                    callee,
                });
                return;
            }
            // An outside container: ask the environment.
            if self.m.is_outside(cur.res) && matches!(cur.kind, DefKind::Module | DefKind::Extern) {
                let mut hit = None;
                'outer: for &t in &ts {
                    for nsx in Namespace::ALL {
                        if self.m.policy.table_ix(nsx) != t {
                            continue;
                        }
                        if let Some(e) = self.m.env.member(cur.res, seg.name, nsx) {
                            hit = Some(Hit {
                                res: e.res,
                                kind: e.kind,
                                vis: e.vis,
                                binding: NONE,
                            });
                            break 'outer;
                        }
                    }
                }
                match hit {
                    Some(h) => {
                        if h.vis != hir_lang::Vis::Public && self.m.policy.visibility_enforced() {
                            self.diag(
                                p,
                                DiagKind::Private {
                                    name: seg.name,
                                    res: h.res,
                                    vis: h.vis,
                                },
                                k,
                                true,
                            );
                        }
                        self.seg_ref(p, k - 1, cur.res, cur.binding);
                        *cur = h;
                        prev_name = Some(seg.name);
                        continue;
                    }
                    None if cur.kind == DefKind::Module => {
                        self.diag(
                            p,
                            DiagKind::Unresolved {
                                name: seg.name,
                                ns,
                                container: Some(container_name),
                                suggestion: None,
                            },
                            k,
                            false,
                        );
                        return;
                    }
                    None => {
                        self.partial(p, *cur, n - k);
                        return;
                    }
                }
            }
            if cur.kind.is_prefix() {
                self.partial(p, *cur, n - k);
                return;
            }
            self.diag(
                p,
                DiagKind::NotAContainer {
                    name: container_name,
                    found: cur.kind,
                },
                k - 1,
                false,
            );
            return;
        }
        if rest > 0 {
            self.partial(p, *cur, rest);
            return;
        }
        self.finish(p, ctx, *cur, count.saturating_sub(1));
    }

    /// Plans a resolved prefix with `unresolved` type-directed segments.
    fn partial(&mut self, p: PathId, cur: Hit, unresolved: usize) {
        let n = self.hir.path(p).segments.len();
        if !cur.kind.is_prefix() {
            let name = self
                .hir
                .list(self.hir.path(p).segments)
                .get(n - unresolved - 1)
                .map(|s| s.name);
            if let Some(name) = name {
                self.diag(
                    p,
                    DiagKind::NotAContainer {
                        name,
                        found: cur.kind,
                    },
                    n - unresolved - 1,
                    false,
                );
            }
            return;
        }
        self.seg_ref(p, n - unresolved - 1, cur.res, cur.binding);
        self.out.plan(p, cur.res, ix(unresolved));
    }

    /// Plans a fully resolved path whose last segment `seg` reached `cur`.
    fn finish(&mut self, p: PathId, ctx: Ctx, cur: Hit, seg: usize) {
        let ns = self.hir.path(p).ns;
        let name = self
            .hir
            .list(self.hir.path(p).segments)
            .get(seg)
            .map(|s| s.name);
        if let Ctx::PatIdent(pat) = ctx {
            if !cur.kind.is_pattern_constant() {
                return;
            }
            self.out.ident_matches.push(pat);
        } else if !cur.kind.fits(ns) {
            if let Some(name) = name {
                self.diag(
                    p,
                    DiagKind::WrongKind {
                        name,
                        ns,
                        found: cur.kind,
                    },
                    seg,
                    false,
                );
            }
            return;
        }
        self.seg_ref(p, seg, cur.res, cur.binding);
        self.out.plan(p, cur.res, 0);
    }

    /// Looks a segment up in one finished table (module-qualified lookups).
    fn in_table(
        &mut self,
        p: PathId,
        s: u32,
        name: Name,
        ns: Ns,
        prefix: bool,
        seg: usize,
    ) -> Option<Start> {
        let ts = self.tables_for(ns, prefix, self.is_callee(p));
        let from = self.module();
        for t in ts {
            match self.m.find(s, t, name) {
                Some(EntryState::One(b)) => {
                    let hit = self.hit_of_binding(b)?;
                    if let Some(x) = self.m.bindings.get(b as usize) {
                        if !self.m.accessible(x.vis, x.home, from) {
                            self.diag(
                                p,
                                DiagKind::Private {
                                    name,
                                    res: x.res,
                                    vis: x.vis,
                                },
                                seg,
                                true,
                            );
                        }
                    }
                    return Some(Start::Hit(hit));
                }
                Some(EntryState::Ambiguous(a, b)) => {
                    self.ambiguous(p, name, a, b, seg);
                    return Some(Start::Done);
                }
                Some(EntryState::Failed(_)) => {
                    self.diag(p, DiagKind::BrokenImport { name }, seg, false);
                    return Some(Start::Done);
                }
                None => {}
            }
        }
        None
    }

    /// The kind of a visible item named `name` in a table the path's
    /// namespace does not search (for "expected a type, found function").
    fn probe_other(&self, name: Name, ns: Ns) -> Option<DefKind> {
        let searched = self.tables_for(ns, false, false);
        (0..TABLES as u8)
            .filter(|t| !searched.contains(t))
            .filter_map(|t| self.top(t, name))
            .find_map(|e| match e.item {
                Item::Table(s, i) => match self
                    .m
                    .scopes
                    .get(s as usize)
                    .and_then(|s| s.table.get(i as usize))
                    .map(|e| e.state)
                {
                    Some(EntryState::One(b)) => self.m.bindings.get(b as usize).map(|b| b.kind),
                    _ => None,
                },
                Item::Binder(_) => Some(DefKind::Local),
            })
    }

    fn ambiguous(&mut self, p: PathId, name: Name, a: u32, b: u32, seg: usize) {
        let res = |x: u32| self.m.bindings.get(x as usize).map_or(Res::Err, |b| b.res);
        let (first, second) = (res(a), res(b));
        self.diag(
            p,
            DiagKind::AmbiguousGlob {
                name,
                first,
                second,
            },
            seg,
            false,
        );
    }

    fn ancestor(&self, levels: u8) -> Option<u32> {
        let mut s = self.module();
        for _ in 0..levels {
            let parent = self.m.scopes.get(s as usize)?.parent;
            s = self.m.scopes.get(parent as usize)?.module;
        }
        (s != NONE).then_some(s)
    }

    fn root_hit(&self, name: Name) -> Option<Hit> {
        if let Some(u) = self.m.root_unit(name) {
            let unit = self.m.units.get(u as usize)?;
            return Some(Hit {
                res: Res::Def(hir_lang::DefId::foreign(
                    unit.id,
                    hir_lang::Def::Item(unit.hir.root()),
                )),
                kind: DefKind::Module,
                vis: hir_lang::Vis::Public,
                binding: NONE,
            });
        }
        self.m.env.root(name).map(|e| Hit {
            res: e.res,
            kind: e.kind,
            vis: e.vis,
            binding: NONE,
        })
    }

    fn prelude_hit(&self, name: Name, ts: &[u8]) -> Option<Hit> {
        for &t in ts {
            for nsx in Namespace::ALL {
                if self.m.policy.table_ix(nsx) != t {
                    continue;
                }
                if let Some(e) = self.m.env.prelude(name, nsx) {
                    return Some(Hit {
                        res: e.res,
                        kind: e.kind,
                        vis: e.vis,
                        binding: NONE,
                    });
                }
            }
        }
        None
    }

    /// A `global` declaration: a global of the unit's root module, or (with
    /// implicit globals) a host global.
    fn global_decl(&mut self, p: PathId, name: Name) -> Start {
        let mut ts: Vec<u8> = Vec::new();
        for ns in self.m.policy.occupies(ItemClass::Global).iter() {
            let t = self.m.policy.table_ix(ns);
            if !ts.contains(&t) {
                ts.push(t);
            }
        }
        for t in ts {
            match self.m.find(self.unit.root_scope, t, name) {
                Some(EntryState::One(b)) => {
                    if let Some(h) = self.hit_of_binding(b) {
                        return Start::Hit(h);
                    }
                }
                Some(EntryState::Ambiguous(a, b)) => {
                    self.ambiguous(p, name, a, b, 0);
                    return Start::Done;
                }
                Some(EntryState::Failed(_)) => {
                    self.diag(p, DiagKind::BrokenImport { name }, 0, false);
                    return Start::Done;
                }
                None => {}
            }
        }
        if self.m.policy.implicit_globals() {
            self.seg_ref(p, 0, Res::Extern(name.sym), NONE);
            self.out.plan(p, Res::Extern(name.sym), 0);
            return Start::Done;
        }
        Start::Unresolved
    }

    /// The first segment of a relative path: binders, visible items, roots,
    /// the prelude.
    fn first(&mut self, p: PathId, ctx: Ctx, name: Name, prefix: bool) -> Start {
        let ns = self.hir.path(p).ns;
        let callee = self.is_callee(p);
        let mut best: Option<((u32, u32), Cand)> = None;
        if ns != Ns::Import {
            if let Some(b) = self.hir.lookup_local(p, name) {
                let (depth, seq) = self
                    .binder_info
                    .get(b.index())
                    .copied()
                    .unwrap_or((0, NONE));
                if seq != NONE {
                    best = Some(((depth, seq), Cand::Binder(b, false)));
                }
            }
        }
        for t in self.tables_for(ns, prefix, callee) {
            let Some(e) = self.top(t, name) else { continue };
            let key = (e.depth, e.seq);
            if best.is_none_or(|(k, _)| key > k) {
                best = Some((
                    key,
                    match e.item {
                        Item::Table(s, i) => Cand::Entry(s, i),
                        Item::Binder(b) => Cand::Binder(b, true),
                    },
                ));
            }
        }
        match best.map(|(_, c)| c) {
            Some(Cand::Binder(b, from_stack)) => self.binder_start(p, ctx, b, prefix, from_stack),
            Some(Cand::Entry(s, i)) => {
                let state = self
                    .m
                    .scopes
                    .get(s as usize)
                    .and_then(|s| s.table.get(i as usize))
                    .map(|e| e.state);
                match state {
                    Some(EntryState::One(b)) => {
                        self.hit_of_binding(b).map_or(Start::Unresolved, Start::Hit)
                    }
                    Some(EntryState::Ambiguous(a, b)) => {
                        self.ambiguous(p, name, a, b, 0);
                        Start::Done
                    }
                    Some(EntryState::Failed(_)) => {
                        if let Ctx::PatIdent(_) = ctx {
                            return Start::Bind;
                        }
                        self.diag(p, DiagKind::BrokenImport { name }, 0, false);
                        Start::Done
                    }
                    None => Start::Unresolved,
                }
            }
            None => {
                let roots_ok = prefix || ns == Ns::Import;
                if roots_ok {
                    if let Some(h) = self.root_hit(name) {
                        return Start::Hit(h);
                    }
                }
                let ts = self.tables_for(ns, prefix, callee);
                self.prelude_hit(name, &ts)
                    .map_or(Start::Unresolved, Start::Hit)
            }
        }
    }

    fn binder_start(
        &mut self,
        p: PathId,
        ctx: Ctx,
        b: BinderId,
        prefix: bool,
        from_stack: bool,
    ) -> Start {
        let ns = self.hir.path(p).ns;
        let n = self.hir.path(p).segments.len();
        let name = self.hir.binder(b).map(|x| x.name);
        let kind = self.hir.binder(b).map(|x| x.kind);
        match ctx {
            Ctx::PatIdent(_) => return Start::Bind,
            Ctx::Import(_) | Ctx::GlobalDecl => return Start::Unresolved,
            Ctx::Normal => {}
        }
        if ns == Ns::Pattern {
            if let Some(name) = name {
                self.diag(
                    p,
                    DiagKind::WrongKind {
                        name,
                        ns,
                        found: DefKind::Local,
                    },
                    0,
                    false,
                );
            }
            return Start::Done;
        }
        if prefix {
            if kind == Some(BinderKind::TypeParam) && ns != Ns::Region {
                self.seg_ref(p, 0, Res::Local(b), NONE);
                self.out.plan(p, Res::Local(b), ix(n.saturating_sub(1)));
                return Start::Done;
            }
            if let Some(name) = name {
                self.diag(
                    p,
                    DiagKind::NotAContainer {
                        name,
                        found: DefKind::Local,
                    },
                    0,
                    false,
                );
            }
            return Start::Done;
        }
        if !from_stack && !self.hir.can_reference(p, b) {
            if let Some(name) = name {
                self.diag(p, DiagKind::CannotCapture { name, binder: b }, 0, false);
            }
            return Start::Done;
        }
        if from_stack && kind.and_then(BinderKind::ns) != Some(ns) {
            // A type parameter reached through the shadow stack by a value
            // path: not nameable here.
            if let Some(name) = name {
                self.diag(
                    p,
                    DiagKind::WrongKind {
                        name,
                        ns,
                        found: DefKind::Local,
                    },
                    0,
                    false,
                );
            }
            return Start::Done;
        }
        self.seg_ref(p, 0, Res::Local(b), NONE);
        self.out.plan(p, Res::Local(b), 0);
        Start::Done
    }

    // -------------------------------------------------------- suggestions

    fn suggest_first(&mut self, p: PathId, name: Name, ns: Ns) -> Option<Name> {
        if self.quiet || !self.sugg.has_budget() {
            return None;
        }
        let mut cands: Vec<Name> = Vec::new();
        // Bounded scans: the candidate list is capped, and so is the number
        // of visible binders examined, so one diagnostic costs O(cap).
        for &b in self.visible.iter().rev().take(4 * MAX_CANDIDATES) {
            if cands.len() >= MAX_CANDIDATES {
                break;
            }
            let Some(binder) = self.hir.binder(b) else {
                continue;
            };
            let fits = match ns {
                Ns::Value => binder.kind.is_value() || binder.kind == BinderKind::ConstParam,
                Ns::Type => binder.kind == BinderKind::TypeParam,
                Ns::Region => binder.kind == BinderKind::Region,
                Ns::Pattern | Ns::Import => false,
            };
            if fits && self.hir.can_reference(p, b) {
                cands.push(binder.name);
            }
        }
        for &t in self.open_tables.iter().rev() {
            if cands.len() >= 2 * MAX_CANDIDATES {
                break;
            }
            let Some(scope) = self.m.scopes.get(t as usize) else {
                continue;
            };
            if matches!(scope.kind, ScopeKind::Type(..))
                && self.m.policy.class_scope() != ClassScope::Lexical
            {
                continue;
            }
            cands.extend(scope.table.iter().map(|e| e.spelling).take(MAX_CANDIDATES));
        }
        cands.extend(self.m.roots.iter().map(|(n, _)| *n).take(MAX_CANDIDATES));
        if self.env_names.is_none() {
            let mut env: Vec<Name> = Vec::new();
            self.m.env.for_each_root(&mut |n| {
                if env.len() < MAX_CANDIDATES {
                    env.push(n);
                }
            });
            self.m.env.for_each_prelude(&mut |n, _| {
                if env.len() < 2 * MAX_CANDIDATES {
                    env.push(n);
                }
            });
            env.sort();
            env.dedup();
            self.env_names = Some(env);
        }
        cands.extend(self.env_names.iter().flatten().copied());
        cands.sort();
        cands.dedup();
        cands.truncate(MAX_CANDIDATES);
        self.sugg.best(self.names, name, &cands)
    }

    fn suggest_in(&mut self, s: u32, name: Name) -> Option<Name> {
        if self.quiet || !self.sugg.has_budget() {
            return None;
        }
        let from = self.module();
        let mut cands: Vec<Name> = Vec::new();
        if let Some(scope) = self.m.scopes.get(s as usize) {
            for e in scope.table.iter().take(MAX_CANDIDATES) {
                let visible = match e.state {
                    EntryState::One(b) => self
                        .m
                        .bindings
                        .get(b as usize)
                        .is_some_and(|x| self.m.accessible(x.vis, x.home, from)),
                    _ => false,
                };
                if visible {
                    cands.push(e.spelling);
                }
            }
        }
        cands.sort();
        cands.dedup();
        self.sugg.best(self.names, name, &cands)
    }
}

/// The table indexes a path segment searches, in order: the module and type
/// tables for a prefix; for a value, the function table first when it is a
/// callee and the constant table first otherwise (one table unless the
/// policy keeps constants apart).
pub(crate) fn tables_for(
    policy: &crate::policy::Policy,
    ns: Ns,
    prefix: bool,
    callee: bool,
) -> Vec<u8> {
    let list: &[Namespace] = if prefix {
        &[Namespace::Module, Namespace::Type]
    } else {
        match ns {
            Ns::Value if callee => &[Namespace::Value, Namespace::Const],
            Ns::Value | Ns::Pattern => &[Namespace::Const, Namespace::Value],
            Ns::Type => &[Namespace::Type],
            Ns::Region => &[],
            Ns::Import => &[
                Namespace::Value,
                Namespace::Type,
                Namespace::Module,
                Namespace::Macro,
                Namespace::Const,
            ],
        }
    };
    let mut out = Vec::with_capacity(list.len());
    for ns in list {
        let t = policy.table_ix(*ns);
        if !out.contains(&t) {
            out.push(t);
        }
    }
    out
}

/// How a first segment started.
enum Start {
    Hit(Hit),
    /// Planned (or diagnosed) already.
    Done,
    /// A bare identifier pattern that binds.
    Bind,
    Unresolved,
}

/// The item that gates an entry's visibility (declare-before-use), if its
/// hoisting is `AfterDecl`.
pub(crate) fn entry_gate(m: &Model<'_>, state: EntryState) -> Option<ItemId> {
    let import_gate = |i: u32| {
        let hoist = m.policy.hoisting(ItemClass::Import);
        (hoist == Hoist::AfterDecl)
            .then(|| m.imports.get(i as usize).map(|imp| imp.item))
            .flatten()
    };
    match state {
        EntryState::One(b) => {
            let binding = m.bindings.get(b as usize)?;
            match binding.origin {
                Origin::Item(i) => (binding.hoist == Hoist::AfterDecl).then_some(i),
                Origin::Import(i) | Origin::Glob(i, _) | Origin::Variant(i, _) => import_gate(i),
                Origin::Env | Origin::Mixin(_) => None,
            }
        }
        EntryState::Failed(i) => import_gate(i),
        EntryState::Ambiguous(..) => None,
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::{model::fixture::*, policy::Policy};

    #[test]
    fn test_entry_gate_follows_hoisting() {
        let mut f = Fixture::new();
        let (g, h) = (f.name("g"), f.name("h"));
        let b1 = f.b.block(&[], None);
        let gi = f.b.func(g, &[], b1);
        let b2 = f.b.block(&[], None);
        let hi = f.b.func(h, &[], b2);
        let root = f.b.module(None, &[gi, hi]);
        let hir = f.finish(root);
        let m = model(hir.clone(), &f.names, Policy::new());
        let rs = m.units[0].root_scope as usize;
        assert!(
            m.scopes[rs]
                .table
                .iter()
                .all(|e| entry_gate(&m, e.state).is_none())
        );
        let after = Policy::new().with_hoisting(ItemClass::Fn, Hoist::AfterDecl);
        let m = model(hir, &f.names, after);
        let gates: Vec<_> = m.scopes[rs]
            .table
            .iter()
            .map(|e| entry_gate(&m, e.state))
            .collect();
        assert!(gates.contains(&Some(gi)));
        assert!(gates.contains(&Some(hi)));
    }

    #[test]
    fn test_unit_out_reports_once_per_path() {
        let mut out = UnitOut {
            plan: alloc::vec![None; 2],
            diagnosed: alloc::vec![false; 2],
            segs: Vec::new(),
            deferred: Vec::new(),
            diags: Vec::new(),
            ident_matches: Vec::new(),
            fallbacks: Vec::new(),
        };
        let p = PathId::from_index(1).unwrap();
        let unit = hir_lang::UnitId::new(0);
        out.diag(unit, p, DiagKind::NoParent, Span::new(0, 1), true);
        assert_eq!(out.plan[1], None, "access errors keep the plan");
        out.diag(unit, p, DiagKind::NoParent, Span::new(0, 1), false);
        assert_eq!(out.plan[1], Some((Res::Err, 0)));
        assert_eq!(out.diags.len(), 1);
    }

    #[test]
    fn test_walk_plans_every_use() {
        let mut f = Fixture::new();
        let (g, missing) = (f.name("g"), f.name("missing"));
        let use_g = f.b.name_expr(g);
        let use_missing = f.b.name_expr(missing);
        let both = f.b.list(&[use_g, use_missing]);
        let t = f.b.expr(hir_lang::Expr::Tuple(both));
        let body = f.b.block(&[], Some(t));
        let gi = f.b.func(g, &[], body);
        let root = f.b.module(None, &[gi]);
        let hir = f.finish(root);
        let (_, outs) = walked(hir, &f.names, Policy::new());
        let errors: Vec<_> = outs[0]
            .plan
            .iter()
            .map(|p| p.map(|(r, _)| r == Res::Err))
            .collect();
        assert_eq!(errors, [Some(false), Some(true)]);
        assert_eq!(outs[0].diags.len(), 1);
    }
}
