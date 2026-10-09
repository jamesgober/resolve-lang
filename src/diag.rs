//! Diagnostics: what resolution reports, with did-you-mean suggestions.

use alloc::string::String;
use core::fmt::Write as _;

use hir_lang::{BinderId, DefId, HirError, Name, NodeRef, Ns, PathRoot, Res, Span, UnitId, Vis};
use intern_lang::Lookup;

use crate::env::DefKind;

/// What went wrong, with the data a tool needs to explain or fix it.
///
/// # Examples
///
/// ```
/// use hir_lang::{Name, Ns, Symbol};
/// use resolve_lang::DiagKind;
///
/// let x = Name::new(Symbol::from_u32(1).unwrap());
/// let k = DiagKind::Unresolved { name: x, ns: Ns::Value, container: None, suggestion: None };
/// assert!(k.is_unresolved());
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum DiagKind {
    /// A name that is not visible here (or, with `container`, that the
    /// container does not define). `suggestion` is the closest visible name
    /// within a small edit distance, if any.
    Unresolved {
        /// The name.
        name: Name,
        /// The syntactic namespace of the path.
        ns: Ns,
        /// The module or type the name was looked up in, for `m::x`.
        container: Option<Name>,
        /// The did-you-mean candidate.
        suggestion: Option<Name>,
    },
    /// A name more than one glob import provides, with different meanings.
    AmbiguousGlob {
        /// The name.
        name: Name,
        /// One meaning.
        first: Res,
        /// Another meaning.
        second: Res,
    },
    /// A name that exists but is not visible from here. The path is still
    /// resolved to it, so tools can navigate.
    Private {
        /// The name.
        name: Name,
        /// What it resolved to.
        res: Res,
        /// Its visibility.
        vis: Vis,
    },
    /// A second definition of a name in one scope and namespace.
    Duplicate {
        /// The name.
        name: Name,
        /// Where the first definition's name is.
        first: Span,
    },
    /// A local of an enclosing function used where it cannot be captured
    /// (inside a nested item, or past a frame that does not capture).
    CannotCapture {
        /// The name.
        name: Name,
        /// The local it would have named.
        binder: BinderId,
    },
    /// A definition of the wrong kind for its position (a function used as a
    /// type, a local named by a constructor pattern).
    WrongKind {
        /// The name.
        name: Name,
        /// The syntactic namespace of the path.
        ns: Ns,
        /// What the name actually is.
        found: DefKind,
    },
    /// A path that continues past something without members (`f::x` where
    /// `f` is a function, or a variant used as a prefix).
    NotAContainer {
        /// The name of the non-container.
        name: Name,
        /// What it is.
        found: DefKind,
    },
    /// A binder that reuses a visible name the policy forbids shadowing.
    Shadowing {
        /// The name.
        name: Name,
        /// The binder it shadows.
        shadowed: BinderId,
    },
    /// A name whose import failed to resolve (the import itself has its own
    /// diagnostic).
    BrokenImport {
        /// The name.
        name: Name,
    },
    /// An import that depends on itself through other imports.
    ImportCycle {
        /// The name the import binds.
        name: Name,
    },
    /// An import that resolved while a glob import of the same scope was
    /// still undetermined, and that the finished glob makes ambiguous.
    ImportAmbiguity {
        /// The name.
        name: Name,
    },
    /// A glob import in a language without them.
    GlobsUnsupported,
    /// An aliased import in a language without them.
    AliasesUnsupported,
    /// A path root the language does not have, or that cannot start an import.
    RootUnsupported {
        /// The root.
        root: PathRoot,
    },
    /// `self::`, `parent::`, or `static::` outside any class, interface, or impl.
    OutsideType {
        /// The root.
        root: PathRoot,
    },
    /// `parent::` in a class with no base class.
    NoParent,
    /// `super::` past the unit's root module.
    SuperBeyondRoot {
        /// The number of levels asked for.
        levels: u8,
    },
    /// Two mixins provide the same member and no `insteadof` rule chooses.
    MixinConflict {
        /// The member name.
        name: Name,
        /// The member taken (the first mixin's).
        first: DefId,
        /// The member dropped.
        second: DefId,
    },
    /// Something that is not a mixin used as one.
    NotAMixin {
        /// What it is.
        found: DefKind,
    },
    /// A mixin rule naming a member no used mixin has.
    UnknownMixinMember {
        /// The member name.
        name: hir_lang::Symbol,
    },
    /// A mixin that uses itself, directly or through other mixins.
    MixinCycle,
    /// The HIR refused a resolution resolve-lang computed. This indicates a
    /// disagreement between this crate and hir-lang's checks; the path is
    /// left as `Res::Err` so the `Hir` stays valid.
    Rejected {
        /// The refusal.
        error: HirError,
    },
}

impl DiagKind {
    /// Whether this is an unresolved-name diagnostic.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::DiagKind;
    ///
    /// assert!(!DiagKind::NoParent.is_unresolved());
    /// ```
    #[must_use]
    pub const fn is_unresolved(&self) -> bool {
        matches!(self, Self::Unresolved { .. })
    }

    /// The did-you-mean suggestion, if this diagnostic has one.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Name, Ns, Symbol};
    /// use resolve_lang::DiagKind;
    ///
    /// let (x, y) = (Name::new(Symbol::from_u32(1).unwrap()), Name::new(Symbol::from_u32(2).unwrap()));
    /// let k = DiagKind::Unresolved { name: x, ns: Ns::Value, container: None, suggestion: Some(y) };
    /// assert_eq!(k.suggestion(), Some(y));
    /// ```
    #[must_use]
    pub const fn suggestion(&self) -> Option<Name> {
        match self {
            Self::Unresolved { suggestion, .. } => *suggestion,
            _ => None,
        }
    }
}

/// One problem found while resolving, located in a unit.
///
/// # Examples
///
/// ```
/// use hir_lang::{Span, UnitId};
/// use intern_lang::Interner;
/// use resolve_lang::{DiagKind, Diagnostic};
///
/// let d = Diagnostic { kind: DiagKind::NoParent, unit: UnitId::new(0), span: Span::new(3, 9), node: None };
/// assert_eq!(d.message(&Interner::new()), "`parent::` used in a class with no base class");
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    /// What went wrong.
    pub kind: DiagKind,
    /// The unit it is in.
    pub unit: UnitId,
    /// Where: the offending name's source span (for an expanded name, the
    /// span its origin records).
    pub span: Span,
    /// The HIR node it is about: usually the path, or the item for
    /// definitions and mixins.
    pub node: Option<NodeRef>,
}

impl Diagnostic {
    /// A one-line English message, with names spelled through `names`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Name, Ns, Span, UnitId};
    /// use intern_lang::Interner;
    /// use resolve_lang::{DiagKind, Diagnostic};
    ///
    /// let mut names = Interner::new();
    /// let (lenght, length) = (Name::new(names.intern("lenght")), Name::new(names.intern("length")));
    /// let d = Diagnostic {
    ///     kind: DiagKind::Unresolved { name: lenght, ns: Ns::Value, container: None, suggestion: Some(length) },
    ///     unit: UnitId::new(0),
    ///     span: Span::new(0, 6),
    ///     node: None,
    /// };
    /// assert_eq!(d.message(&names), "cannot find value `lenght` in this scope; did you mean `length`?");
    /// ```
    #[must_use]
    pub fn message<L: Lookup>(&self, names: &L) -> String {
        let mut out = String::new();
        let n = |name: Name| -> String {
            names
                .resolve_with(name.sym, |s: &str| String::from(s))
                .unwrap_or_else(|| String::from("?"))
        };
        // Writing into a String cannot fail; the results are discarded on
        // purpose (`fmt::Write for String` is infallible).
        let _infallible = match self.kind {
            DiagKind::Unresolved {
                name,
                ns,
                container,
                suggestion,
            } => {
                let r = match container {
                    Some(c) => write!(out, "cannot find `{}` in `{}`", n(name), n(c)),
                    None => write!(
                        out,
                        "cannot find {} `{}` in this scope",
                        ns_word(ns),
                        n(name)
                    ),
                };
                match suggestion {
                    Some(s) => write!(out, "; did you mean `{}`?", n(s)),
                    None => r,
                }
            }
            DiagKind::AmbiguousGlob { name, .. } => write!(
                out,
                "`{}` is ambiguous: more than one glob import provides it",
                n(name)
            ),
            DiagKind::Private { name, vis, .. } => {
                write!(out, "`{}` is {}", n(name), vis_word(vis))
            }
            DiagKind::Duplicate { name, .. } => {
                write!(out, "`{}` is defined more than once in this scope", n(name))
            }
            DiagKind::CannotCapture { name, .. } => write!(
                out,
                "cannot use local `{}` here: it belongs to an enclosing function",
                n(name)
            ),
            DiagKind::WrongKind { name, ns, found } => write!(
                out,
                "expected {}, found {} `{}`",
                expected_word(ns),
                found.name(),
                n(name)
            ),
            DiagKind::NotAContainer { name, found } => write!(
                out,
                "`{}` is a {}, which has no members",
                n(name),
                found.name()
            ),
            DiagKind::Shadowing { name, .. } => write!(
                out,
                "`{}` shadows a visible local, which this language forbids",
                n(name)
            ),
            DiagKind::BrokenImport { name } => write!(
                out,
                "`{}` comes from an import that failed to resolve",
                n(name)
            ),
            DiagKind::ImportCycle { name } => {
                write!(out, "the import of `{}` depends on itself", n(name))
            }
            DiagKind::ImportAmbiguity { name } => write!(
                out,
                "the import of `{}` is ambiguous with a glob import in the same scope",
                n(name)
            ),
            DiagKind::GlobsUnsupported => {
                write!(out, "glob imports are not supported by this language")
            }
            DiagKind::AliasesUnsupported => {
                write!(out, "import aliases are not supported by this language")
            }
            DiagKind::RootUnsupported { root } => {
                write!(out, "`{}` is not supported here", root_word(root))
            }
            DiagKind::OutsideType { root } => write!(
                out,
                "`{}` used outside a class, interface, or impl",
                root_word(root)
            ),
            DiagKind::NoParent => write!(out, "`parent::` used in a class with no base class"),
            DiagKind::SuperBeyondRoot { levels } => write!(
                out,
                "`super::` {} level(s) up goes past the root module",
                levels
            ),
            DiagKind::MixinConflict { name, .. } => write!(
                out,
                "more than one mixin provides `{}`; choose one with `insteadof`",
                n(name)
            ),
            DiagKind::NotAMixin { found } => {
                write!(out, "expected a mixin, found {}", found.name())
            }
            DiagKind::UnknownMixinMember { name } => write!(
                out,
                "no mixin used here has a member `{}`",
                n(Name::new(name))
            ),
            DiagKind::MixinCycle => write!(out, "this mixin uses itself"),
            DiagKind::Rejected { error } => {
                write!(out, "the HIR refused this resolution: {error}")
            }
        };
        out
    }
}

const fn ns_word(ns: Ns) -> &'static str {
    match ns {
        Ns::Value => "value",
        Ns::Type => "type",
        Ns::Pattern => "pattern",
        Ns::Region => "region",
        Ns::Import => "import",
    }
}

const fn expected_word(ns: Ns) -> &'static str {
    match ns {
        Ns::Value => "a value",
        Ns::Type => "a type",
        Ns::Pattern => "a constant, variant, or record",
        Ns::Region => "a region",
        Ns::Import => "an importable item",
    }
}

const fn vis_word(vis: Vis) -> &'static str {
    match vis {
        Vis::Private => "private",
        Vis::Protected => "protected",
        Vis::Package => "package-private",
        Vis::Public => "public",
    }
}

const fn root_word(root: PathRoot) -> &'static str {
    match root {
        PathRoot::Relative => "a relative path",
        PathRoot::Global => "::",
        PathRoot::SelfModule => "self::",
        PathRoot::Super(_) => "super::",
        PathRoot::SelfType => "self::",
        PathRoot::ParentType => "parent::",
        PathRoot::StaticType => "static::",
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;
    use intern_lang::Interner;

    fn diag(kind: DiagKind) -> Diagnostic {
        Diagnostic {
            kind,
            unit: UnitId::new(0),
            span: Span::new(0, 1),
            node: None,
        }
    }

    #[test]
    fn test_every_kind_renders_a_message() {
        let mut names = Interner::new();
        let x = Name::new(names.intern("x"));
        let b = BinderId::from_index(0).unwrap();
        let d = DefId::foreign(
            UnitId::new(1),
            hir_lang::Def::Item(hir_lang::ItemId::from_index(0).unwrap()),
        );
        let kinds = [
            DiagKind::Unresolved {
                name: x,
                ns: Ns::Type,
                container: Some(x),
                suggestion: None,
            },
            DiagKind::AmbiguousGlob {
                name: x,
                first: Res::Err,
                second: Res::Err,
            },
            DiagKind::Private {
                name: x,
                res: Res::Err,
                vis: Vis::Protected,
            },
            DiagKind::Duplicate {
                name: x,
                first: Span::new(0, 1),
            },
            DiagKind::CannotCapture { name: x, binder: b },
            DiagKind::WrongKind {
                name: x,
                ns: Ns::Pattern,
                found: DefKind::Fn,
            },
            DiagKind::NotAContainer {
                name: x,
                found: DefKind::Fn,
            },
            DiagKind::Shadowing {
                name: x,
                shadowed: b,
            },
            DiagKind::BrokenImport { name: x },
            DiagKind::ImportCycle { name: x },
            DiagKind::ImportAmbiguity { name: x },
            DiagKind::GlobsUnsupported,
            DiagKind::AliasesUnsupported,
            DiagKind::RootUnsupported {
                root: PathRoot::StaticType,
            },
            DiagKind::OutsideType {
                root: PathRoot::SelfType,
            },
            DiagKind::NoParent,
            DiagKind::SuperBeyondRoot { levels: 2 },
            DiagKind::MixinConflict {
                name: x,
                first: d,
                second: d,
            },
            DiagKind::NotAMixin {
                found: DefKind::Sum,
            },
            DiagKind::UnknownMixinMember { name: x.sym },
            DiagKind::MixinCycle,
            DiagKind::Rejected {
                error: HirError::RootNotModule,
            },
        ];
        for k in kinds {
            let m = diag(k).message(&names);
            assert!(!m.is_empty());
            assert!(!m.contains('?') || k.is_unresolved(), "{m}");
        }
        assert_eq!(diag(kinds[0]).message(&names), "cannot find `x` in `x`");
        assert_eq!(diag(kinds[2]).message(&names), "`x` is protected");
    }

    #[test]
    fn test_message_survives_unknown_symbol() {
        let names = Interner::new();
        let ghost = Name::new(hir_lang::Symbol::from_u32(77).unwrap());
        let m = diag(DiagKind::BrokenImport { name: ghost }).message(&names);
        assert!(m.contains("`?`"));
    }
}
