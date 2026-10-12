//! PHP traits (mixins) under `Policy::php()`: the member tables resolve-lang
//! builds against a model of PHP 8's `zend_traits_copy_functions` and
//! `zend_add_trait_method`, on random graphs of mixins that use mixins, with
//! `insteadof` and `as` rules PHP accepts and abstract methods, plus the
//! worked cases the model first disagreed on (bcgen-lang 0.4 found them with
//! the same model in its `tests/mixins.rs`).

#![allow(clippy::unwrap_used, clippy::expect_used)]

mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::{Kit, item_res, kinds, messages, res};
use hir_lang::{
    FnDef, Hir, Ident, ItemId, ItemKind, MixinAction, MixinRule, PathRoot, Res, Span, Ty, UnitId,
    Vis,
};
use intern_lang::Interner;
use proptest::prelude::*;
use resolve_lang::{DiagKind, Namespace, Policy, Resolver};

// ------------------------------------------------------------ build helpers

fn method(k: &mut Kit, name: &str, vis: Vis, abstract_: bool) -> ItemId {
    let body = (!abstract_).then(|| k.block(&[], None));
    k.item(
        name,
        ItemKind::Fn(FnDef {
            body,
            ..FnDef::default()
        }),
        vis,
    )
}

fn rule(k: &mut Kit, from: Option<&str>, name: &str, action: MixinAction) -> MixinRule {
    let from = from.map(|f| k.ty(&[f]).0);
    MixinRule {
        method: Ident::new(k.name(name).sym, Span::empty(0)),
        from,
        action,
    }
}

fn alias(
    k: &mut Kit,
    from: Option<&str>,
    name: &str,
    new: Option<&str>,
    vis: Option<Vis>,
) -> MixinRule {
    let name_id = new.map(|n| k.ident(n));
    rule(k, from, name, MixinAction::Alias { name: name_id, vis })
}

fn insteadof(k: &mut Kit, from: &str, name: &str, others: &[&str]) -> MixinRule {
    let tys: Vec<_> = others.iter().map(|o| k.ty(&[o]).0).collect();
    let list = k.b.list(&tys);
    rule(k, Some(from), name, MixinAction::Insteadof(list))
}

fn use_mixins(k: &mut Kit, mixins: &[&str], rules: &[MixinRule]) -> ItemId {
    let tys: Vec<_> = mixins.iter().map(|m| k.ty(&[m]).0).collect();
    k.mixin_use(&tys, rules)
}

/// The member of `class` named `name` in the value table, if any:
/// (resolution, visibility).
fn member(
    r: &resolve_lang::Resolution,
    names: &Interner,
    class: ItemId,
    name: &str,
) -> Option<(Res, Vis)> {
    r.units()[0]
        .members(class)?
        .iter()
        .find(|m| m.namespace == Namespace::Value && names.resolve(m.name.sym) == Some(name))
        .map(|m| (m.res, m.vis))
}

fn php(hir: Hir, k: &Kit) -> resolve_lang::Resolution {
    Resolver::new(Policy::php()).resolve(hir, &k.names).unwrap()
}

// ------------------------------------------------------------ worked cases

/// trait A { function hi() {} }  trait B { function hi() {} }
/// class C { use A, B { A::hi insteadof B; B::hi as protected; } }
/// The visibility-only rule names the method of B that `insteadof` excluded:
/// there is no copy to change, so `hi` stays A's, public. (0.4.0 brought B's
/// back as protected.)
#[test]
fn test_visibility_rule_on_an_excluded_method_changes_nothing() {
    let mut k = Kit::new();
    let a_hi = method(&mut k, "hi", Vis::Public, false);
    let a = k.class("A", &[], &[a_hi], true);
    let b_hi = method(&mut k, "hi", Vis::Public, false);
    let b = k.class("B", &[], &[b_hi], true);
    let r1 = insteadof(&mut k, "A", "hi", &["B"]);
    let r2 = alias(&mut k, Some("B"), "hi", None, Some(Vis::Protected));
    let u = use_mixins(&mut k, &["A", "B"], &[r1, r2]);
    let c = k.class("C", &[], &[u], false);
    let hir = k.finish(&[a, b, c]);
    let r = php(hir, &k);
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(
        member(&r, &k.names, c, "hi"),
        Some((item_res(0, a_hi), Vis::Public))
    );
    let _ = b_hi;
}

/// trait A { function m() {} }  trait B { function x() {} }
/// class C { use A, B { B::x as m; } }
/// The alias is a second `m`: PHP refuses it ("collision"), and the first
/// `m` (A's) stays; 0.4.0 let the alias replace it silently.
#[test]
fn test_alias_does_not_replace_a_member_an_earlier_mixin_gave() {
    let mut k = Kit::new();
    let a_m = method(&mut k, "m", Vis::Public, false);
    let a = k.class("A", &[], &[a_m], true);
    let b_x = method(&mut k, "x", Vis::Public, false);
    let b = k.class("B", &[], &[b_x], true);
    let r1 = alias(&mut k, Some("B"), "x", Some("m"), None);
    let u = use_mixins(&mut k, &["A", "B"], &[r1]);
    let c = k.class("C", &[], &[u], false);
    let hir = k.finish(&[a, b, c]);
    let r = php(hir, &k);
    assert_eq!(
        member(&r, &k.names, c, "m"),
        Some((item_res(0, a_m), Vis::Public))
    );
    assert!(
        kinds(&r)
            .iter()
            .any(|d| matches!(d, DiagKind::MixinConflict { .. })),
        "{:?}",
        messages(&r, &k.names)
    );
    // The aliased method is still there under its own name.
    assert_eq!(
        member(&r, &k.names, c, "x"),
        Some((item_res(0, b_x), Vis::Public))
    );
}

/// trait A { abstract function m(); }  trait B { function m() {} }
/// trait Q { function m() {} abstract function n(); }  trait R { function n() {} }
/// class C { use A, B; }   class D { use B, A; }
/// An abstract method only has to be satisfied: it never replaces a member,
/// and a concrete one replaces an abstract one an earlier mixin brought.
#[test]
fn test_abstract_mixin_methods_never_hide_concrete_ones() {
    let mut k = Kit::new();
    let a_m = method(&mut k, "m", Vis::Public, true);
    let a = k.class("A", &[], &[a_m], true);
    let b_m = method(&mut k, "m", Vis::Public, false);
    let b = k.class("B", &[], &[b_m], true);
    let u1 = use_mixins(&mut k, &["A", "B"], &[]);
    let c = k.class("C", &[], &[u1], false);
    let u2 = use_mixins(&mut k, &["B", "A"], &[]);
    let d = k.class("D", &[], &[u2], false);
    let hir = k.finish(&[a, b, c, d]);
    let r = php(hir, &k);
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    let want = Some((item_res(0, b_m), Vis::Public));
    assert_eq!(member(&r, &k.names, c, "m"), want);
    assert_eq!(member(&r, &k.names, d, "m"), want);
}

/// trait A { const hi = 1; function hi() {} }  trait B { const hi = 2; function hi() {} }
/// class C { use A, B { A::hi insteadof B; } }
/// The rule is about methods: B's constant `hi` is not a method and is not
/// excluded (it is a conflict with A's constant, which PHP reports).
#[test]
fn test_rules_name_methods_not_constants() {
    let mut k = Kit::new();
    let a_c = k.constant("hi", Vis::Public);
    let a_hi = method(&mut k, "hi", Vis::Public, false);
    let a = k.class("A", &[], &[a_c, a_hi], true);
    let b_hi = method(&mut k, "hi", Vis::Public, false);
    let b = k.class("B", &[], &[b_hi], true);
    let r1 = insteadof(&mut k, "A", "hi", &["B"]);
    let u = use_mixins(&mut k, &["A", "B"], &[r1]);
    let c = k.class("C", &[], &[u], false);
    // `A::hi` as a rule target must find the method although a constant of
    // that name exists too; a constant alone is not a method.
    let a2_c = k.constant("only", Vis::Public);
    let a2 = k.class("A2", &[], &[a2_c], true);
    let r2 = alias(&mut k, None, "only", Some("x"), None);
    let u2 = use_mixins(&mut k, &["A2"], &[r2]);
    let c2 = k.class("C2", &[], &[u2], false);
    let hir = k.finish(&[a, b, c, a2, c2]);
    let r = php(hir, &k);
    assert_eq!(
        member(&r, &k.names, c, "hi"),
        Some((item_res(0, a_hi), Vis::Public))
    );
    // C2: the rule names no method, as in PHP.
    assert!(
        kinds(&r)
            .iter()
            .any(|d| matches!(d, DiagKind::UnknownMixinMember { .. })),
        "{:?}",
        messages(&r, &k.names)
    );
    assert_eq!(member(&r, &k.names, c2, "x"), None);
}

/// trait T { function m() {} }
/// trait U { use T { m as protected; } }   trait V { use T; }
/// class C { use U, V; }
/// The same function at two visibilities arrives twice: PHP's collision.
#[test]
fn test_same_method_at_two_visibilities_is_a_conflict() {
    let mut k = Kit::new();
    let t_m = method(&mut k, "m", Vis::Public, false);
    let t = k.class("T", &[], &[t_m], true);
    let r1 = alias(&mut k, None, "m", None, Some(Vis::Protected));
    let uu = use_mixins(&mut k, &["T"], &[r1]);
    let u = k.class("U", &[], &[uu], true);
    let vu = use_mixins(&mut k, &["T"], &[]);
    let v = k.class("V", &[], &[vu], true);
    let cu = use_mixins(&mut k, &["U", "V"], &[]);
    let c = k.class("C", &[], &[cu], false);
    let hir = k.finish(&[t, u, v, c]);
    let r = php(hir, &k);
    assert!(
        kinds(&r)
            .iter()
            .any(|d| matches!(d, DiagKind::MixinConflict { .. })),
        "{:?}",
        messages(&r, &k.names)
    );
    // The first mixin's copy stays.
    assert_eq!(
        member(&r, &k.names, c, "m"),
        Some((item_res(0, t_m), Vis::Protected))
    );
}

/// The same function reaching a class twice at one visibility (a diamond of
/// mixins) is no conflict.
#[test]
fn test_diamond_of_mixins_is_no_conflict() {
    let mut k = Kit::new();
    let t_m = method(&mut k, "m", Vis::Public, false);
    let t = k.class("T", &[], &[t_m], true);
    let uu = use_mixins(&mut k, &["T"], &[]);
    let u = k.class("U", &[], &[uu], true);
    let vu = use_mixins(&mut k, &["T"], &[]);
    let v = k.class("V", &[], &[vu], true);
    let cu = use_mixins(&mut k, &["U", "V"], &[]);
    let c = k.class("C", &[], &[cu], false);
    let hir = k.finish(&[t, u, v, c]);
    let r = php(hir, &k);
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names));
    assert_eq!(
        member(&r, &k.names, c, "m"),
        Some((item_res(0, t_m), Vis::Public))
    );
}

/// `self::name` inside a class sees the table: a protected alias is
/// reachable from the class and reported from outside.
#[test]
fn test_mixin_visibility_reaches_paths() {
    let mut k = Kit::new();
    let a_hi = method(&mut k, "hi", Vis::Public, false);
    let a = k.class("A", &[], &[a_hi], true);
    let r1 = alias(&mut k, Some("A"), "hi", Some("secret"), Some(Vis::Private));
    let u = use_mixins(&mut k, &["A"], &[r1]);
    let (inside, p_in) = k.use_root(&["secret"], PathRoot::SelfType);
    let body = k.block(&[], Some(inside));
    let reads = method_with_body(&mut k, "reads", body);
    let c = k.class("C", &[], &[u, reads], false);
    let (outside, p_out) = k.use_(&["C", "secret"]);
    let fb = k.block(&[], Some(outside));
    let main = k.func("main", &[], fb);
    let hir = k.finish(&[a, c, main]);
    let r = php(hir, &k);
    assert_eq!(res(&r, 0, p_in).0, item_res(0, a_hi));
    assert_eq!(res(&r, 0, p_out).0, item_res(0, a_hi));
    let ks = kinds(&r);
    assert_eq!(ks.len(), 1, "{:?}", messages(&r, &k.names));
    assert!(matches!(
        ks[0],
        DiagKind::Private {
            vis: Vis::Private,
            ..
        }
    ));
}

fn method_with_body(k: &mut Kit, name: &str, body: hir_lang::ExprId) -> ItemId {
    k.func_vis(name, &[], body, Vis::Public)
}

/// trait A { m0 .. m(n-1) }   trait B { m0 .. m(n-1) }
/// class C { use A, B { A::mi insteadof B; B::mi as bi; (for every i) } }
/// Tens of thousands of members and rules resolve in one pass of sorted
/// lookups; a rescan of the rules or the members per member would take
/// minutes at this size.
#[test]
fn test_many_members_and_rules_stay_linear_in_practice() {
    let n = 30_000usize;
    let mut k = Kit::new();
    let mut a_items = Vec::new();
    let mut b_items = Vec::new();
    for i in 0..n {
        a_items.push(method(&mut k, &format!("m{i}"), Vis::Public, false));
        b_items.push(method(&mut k, &format!("m{i}"), Vis::Public, false));
    }
    let a = k.class("A", &[], &a_items, true);
    let b = k.class("B", &[], &b_items, true);
    let mut rules = Vec::new();
    for i in 0..n {
        rules.push(insteadof(&mut k, "A", &format!("m{i}"), &["B"]));
        rules.push(alias(
            &mut k,
            Some("B"),
            &format!("m{i}"),
            Some(&format!("b{i}")),
            Some(Vis::Protected),
        ));
    }
    let u = use_mixins(&mut k, &["A", "B"], &rules);
    let c = k.class("C", &[], &[u], false);
    let hir = k.finish(&[a, b, c]);
    let r = php(hir, &k);
    assert!(r.is_clean(), "{:?}", messages(&r, &k.names).first());
    let members = r.units()[0].members(c).unwrap();
    assert_eq!(members.len(), 2 * n);
    for i in [0, 1, n / 2, n - 1] {
        assert_eq!(
            member(&r, &k.names, c, &format!("m{i}")),
            Some((item_res(0, a_items[i]), Vis::Public))
        );
        assert_eq!(
            member(&r, &k.names, c, &format!("b{i}")),
            Some((item_res(0, b_items[i]), Vis::Protected))
        );
    }
}

// ------------------------------------------------------ differential model

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
}

fn vis(rng: &mut Rng) -> Vis {
    [Vis::Public, Vis::Public, Vis::Protected, Vis::Private][rng.below(4) as usize]
}

const METHODS: usize = 4;

/// A `use` of `mixins` (by index) whose rules PHP accepts: every name two
/// used mixins provide gets an `insteadof` choosing one; aliases take fresh
/// names; an unqualified rule names a method only one used mixin has.
/// Returns the item and the names the use brings in.
fn mixin_use(
    k: &mut Kit,
    rng: &mut Rng,
    mixins: &[usize],
    provides: &[BTreeSet<String>],
    fresh: &mut u32,
) -> (ItemId, BTreeSet<String>) {
    let names: Vec<String> = mixins.iter().map(|m| format!("T{m}")).collect();
    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let mut rules = Vec::new();
    let mut brought: BTreeSet<String> = BTreeSet::new();
    let mut providers: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for &m in mixins {
        for n in &provides[m] {
            providers.entry(n.clone()).or_default().push(m);
            let _ = brought.insert(n.clone());
        }
    }
    for (name, ps) in &providers {
        if ps.len() < 2 {
            continue;
        }
        let w = ps[rng.below(ps.len() as u64) as usize];
        let others: Vec<String> = ps
            .iter()
            .filter(|&&o| o != w)
            .map(|o| format!("T{o}"))
            .collect();
        let others: Vec<&str> = others.iter().map(String::as_str).collect();
        rules.push(insteadof(k, &format!("T{w}"), name, &others));
    }
    let all: Vec<(String, Vec<usize>)> = providers.into_iter().collect();
    for _ in 0..rng.below(4) {
        if all.is_empty() {
            break;
        }
        let (name, ps) = &all[rng.below(all.len() as u64) as usize];
        let single = ps.len() == 1;
        let t = ps[rng.below(ps.len() as u64) as usize];
        let qualified = !single || rng.below(2) == 0;
        let from = qualified.then(|| format!("T{t}"));
        if rng.below(2) == 0 {
            *fresh += 1;
            let new = format!("a{fresh}");
            let v = (rng.below(2) == 0).then(|| vis(rng));
            rules.push(alias(k, from.as_deref(), name, Some(&new), v));
            let _ = brought.insert(new);
        } else {
            let v = vis(rng);
            rules.push(alias(k, from.as_deref(), name, None, Some(v)));
        }
    }
    (use_mixins(k, &refs, &rules), brought)
}

/// Builds a random program; returns it with the class items and every
/// method name a class may have.
fn program(seed: u64) -> (Hir, Kit, Vec<ItemId>, Vec<String>) {
    let mut rng = Rng(seed | 1);
    let mut k = Kit::new();
    let nm = 1 + rng.below(4) as usize;
    let mut provides: Vec<BTreeSet<String>> = Vec::new();
    let mut fresh = 0u32;
    let mut items = Vec::new();
    for t in 0..nm {
        let mut members = Vec::new();
        let mut mine: BTreeSet<String> = BTreeSet::new();
        for m in 0..METHODS {
            if rng.below(2) == 0 {
                let v = vis(&mut rng);
                let abstract_ = rng.below(4) == 0;
                members.push(method(&mut k, &format!("m{m}"), v, abstract_));
                let _ = mine.insert(format!("m{m}"));
            }
        }
        // Mixins use earlier mixins (no cycles).
        if t > 0 && rng.below(2) == 0 {
            let n = 1 + rng.below(t.min(2) as u64) as usize;
            let mut used: Vec<usize> = (0..n).map(|_| rng.below(t as u64) as usize).collect();
            used.sort_unstable();
            used.dedup();
            let (u, brought) = mixin_use(&mut k, &mut rng, &used, &provides, &mut fresh);
            members.push(u);
            mine.extend(brought);
        }
        provides.push(mine);
        items.push(k.class(&format!("T{t}"), &[], &members, true));
    }
    let mut classes = Vec::new();
    let mut names: BTreeSet<String> = BTreeSet::new();
    for c in 0..1 + rng.below(3) as usize {
        let mut members = Vec::new();
        for m in 0..METHODS {
            if rng.below(4) == 0 {
                members.push(method(&mut k, &format!("m{m}"), Vis::Public, false));
                let _ = names.insert(format!("m{m}"));
            }
        }
        let n = 1 + rng.below(nm.min(3) as u64) as usize;
        let mut used: Vec<usize> = (0..n).map(|_| rng.below(nm as u64) as usize).collect();
        used.sort_unstable();
        used.dedup();
        let (u, brought) = mixin_use(&mut k, &mut rng, &used, &provides, &mut fresh);
        names.extend(brought);
        members.push(u);
        let class = k.class(&format!("C{c}"), &[], &members, false);
        classes.push(class);
        items.push(class);
    }
    let hir = k.finish(&items);
    (hir, k, classes, names.into_iter().collect())
}

/// One method of a model table: its item and visibility, and whether it is
/// the container's own (own members win over mixin ones).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Fm {
    item: ItemId,
    vis: Vis,
    own: bool,
}

type Table = Vec<(String, Fm)>;

/// PHP's effective method table of `container` (a class or mixin item), in
/// insertion order, computed from the HIR (mixins first, memoized).
fn php_table(
    hir: &Hir,
    names: &Interner,
    container: ItemId,
    memo: &mut BTreeMap<ItemId, Table>,
) -> Table {
    if let Some(t) = memo.get(&container) {
        return t.clone();
    }
    let ItemKind::Class(def) = hir.item(container).kind else {
        return Vec::new();
    };
    let text = |sym: hir_lang::Symbol| names.resolve(sym).unwrap_or("").to_string();
    let item_of = |ty: hir_lang::TyId| -> Option<ItemId> {
        let Ty::Path(p) = *hir.ty(ty) else {
            return None;
        };
        match hir.path(p).res {
            Res::Def(d) => match d.def() {
                hir_lang::Def::Item(i) => Some(i),
                hir_lang::Def::Variant(_) => None,
            },
            _ => None,
        }
    };
    let mut table: Table = Vec::new();
    for &m in hir.list(def.items) {
        let it = *hir.item(m);
        if let (ItemKind::Fn(_), Some(n)) = (it.kind, it.name) {
            table.push((
                text(n.sym),
                Fm {
                    item: m,
                    vis: it.vis,
                    own: true,
                },
            ));
        }
    }
    for &u in hir.list(def.items) {
        let ItemKind::MixinUse(ud) = hir.item(u).kind else {
            continue;
        };
        let traits: Vec<ItemId> = hir
            .list(ud.mixins)
            .iter()
            .filter_map(|&t| item_of(t))
            .collect();
        let tables: Vec<Table> = traits
            .iter()
            .map(|&t| php_table(hir, names, t, memo))
            .collect();
        let mut exclude: BTreeSet<(ItemId, String)> = BTreeSet::new();
        let mut aliases: Vec<(ItemId, String, Option<String>, Option<Vis>)> = Vec::new();
        for r in hir.list(ud.rules) {
            let method = text(r.method.sym);
            match r.action {
                MixinAction::Insteadof(others) => {
                    for &o in hir.list(others) {
                        if let Some(oi) = item_of(o) {
                            let _ = exclude.insert((oi, method.clone()));
                        }
                    }
                }
                MixinAction::Alias { name, vis } => {
                    let t = match r.from.and_then(item_of) {
                        Some(t) => Some(t),
                        // Unqualified: the one used trait that has it.
                        None => traits
                            .iter()
                            .zip(&tables)
                            .find(|(_, tab)| tab.iter().any(|(n, _)| *n == method))
                            .map(|(&t, _)| t),
                    };
                    if let Some(t) = t {
                        aliases.push((t, method, name.map(|n| text(n.sym)), vis));
                    }
                }
            }
        }
        for (&t, tab) in traits.iter().zip(&tables) {
            for (name, f) in tab {
                for (at, am, new, v) in &aliases {
                    if *at == t && am == name {
                        if let Some(new) = new {
                            let copy = Fm {
                                vis: v.unwrap_or(f.vis),
                                own: false,
                                ..*f
                            };
                            add(hir, &mut table, new, copy);
                        }
                    }
                }
                if !exclude.contains(&(t, name.clone())) {
                    let mut copy = Fm { own: false, ..*f };
                    for (at, am, new, v) in &aliases {
                        if *at == t && am == name && new.is_none() {
                            if let Some(v) = v {
                                copy.vis = *v;
                            }
                        }
                    }
                    add(hir, &mut table, name, copy);
                }
            }
        }
    }
    let _ = memo.insert(container, table.clone());
    table
}

fn is_abstract(hir: &Hir, item: ItemId) -> bool {
    matches!(hir.item(item).kind, ItemKind::Fn(def) if def.body.is_none())
}

/// `zend_add_trait_method`: an own member wins; an abstract method never
/// replaces anything; a concrete one replaces an abstract one; the generator
/// makes no other conflict.
fn add(hir: &Hir, table: &mut Table, name: &str, f: Fm) {
    match table.iter().position(|(n, _)| n == name) {
        None => table.push((name.to_string(), f)),
        Some(i) => {
            let e = table[i].1;
            if !e.own && !is_abstract(hir, f.item) && is_abstract(hir, e.item) {
                table[i].1 = f;
            }
        }
    }
}

fn check(seed: u64) -> Result<(), TestCaseError> {
    let (hir, k, classes, methods) = program(seed);
    let r = php(hir, &k);
    // The programs are ones PHP accepts: resolution is clean.
    prop_assert!(r.is_clean(), "seed {}: {:?}", seed, messages(&r, &k.names));
    let hir = r.hir(UnitId::new(0)).unwrap();
    let mut memo = BTreeMap::new();
    for &class in &classes {
        let table = php_table(hir, &k.names, class, &mut memo);
        for name in &methods {
            let model = table.iter().find(|(n, _)| n == name).map(|(_, f)| *f);
            let got = member(&r, &k.names, class, name);
            let want = model.map(|f| (item_res(0, f.item), f.vis));
            prop_assert_eq!(got, want, "seed {} class {:?} method {}", seed, class, name);
        }
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1500))]

    /// Every member of every class is the method (and visibility) PHP's trait
    /// copying leaves.
    #[test]
    fn prop_member_tables_match_the_php_model(seed in any::<u64>()) {
        check(seed)?;
    }
}

/// The generator exercises what the model is about: excluded methods with
/// visibility rules, aliases, nested uses, abstract methods.
#[test]
fn test_generator_covers_rules_aliases_nesting_and_abstract_methods() {
    let (mut excluded_vis, mut aliases, mut nested, mut abstracts) = (0, 0, 0, 0);
    for seed in 0..400u64 {
        let (hir, _k, _classes, _) = program(seed);
        for i in 0..hir.count(hir_lang::IdKind::Item) {
            let item = ItemId::from_index(i).unwrap();
            match hir.item(item).kind {
                ItemKind::MixinUse(u) => {
                    for rule in hir.list(u.rules) {
                        match rule.action {
                            MixinAction::Insteadof(_) => excluded_vis += 1,
                            MixinAction::Alias { name, .. } => {
                                aliases += usize::from(name.is_some())
                            }
                        }
                    }
                }
                ItemKind::Class(c) if c.mixin => {
                    nested += hir
                        .list(c.items)
                        .iter()
                        .filter(|m| matches!(hir.item(**m).kind, ItemKind::MixinUse(_)))
                        .count();
                }
                ItemKind::Fn(f) if f.body.is_none() => abstracts += 1,
                _ => {}
            }
        }
    }
    assert!(
        excluded_vis > 100 && aliases > 100 && nested > 50 && abstracts > 100,
        "{excluded_vis} {aliases} {nested} {abstracts}"
    );
}
