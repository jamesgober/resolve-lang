//! # resolve_lang
//!
//! Name resolution over HIR: every path and bare-identifier pattern of a
//! [`hir_lang::Hir`] is bound to the binder or definition it names, under a
//! language's scoping [`Policy`], with diagnostics (did-you-mean included)
//! for what does not resolve, and a persistent [`Index`] of definitions and
//! references for go-to-definition, find-references, rename, and document
//! symbols.
//!
//! ## The lazy path
//!
//! [`resolve`] takes a unit and the interner its names came from, and
//! returns the resolved unit, its diagnostics, and the index:
//!
//! ```
//! use hir_lang::{Builder, Expr, Name, Res};
//! use intern_lang::Interner;
//!
//! // fn double(n) { n }   fn main() { double }
//! let mut names = Interner::new();
//! let (n, double) = (Name::new(names.intern("n")), Name::new(names.intern("double")));
//! let mut b = Builder::new();
//! let (param, n_binder) = b.local_param(n);
//! let use_n = b.name_expr(n);
//! let body = b.block(&[], Some(use_n));
//! let f = b.func(double, &[param], body);
//! let use_double = b.name_expr(double);
//! let main_body = b.block(&[], Some(use_double));
//! let main = b.func(Name::new(names.intern("main")), &[], main_body);
//! let root = b.module(None, &[f, main]);
//! let hir = b.finish(root)?;
//! let unit = hir.unit();
//!
//! let res = resolve_lang::resolve(hir, &names)?;
//! assert!(res.is_clean());
//! let hir = res.hir(unit).unwrap();
//! let Expr::Path(p) = *hir.expr(use_n) else { unreachable!() };
//! assert_eq!(hir.path(p).res, Res::Local(n_binder));
//! let Expr::Path(p) = *hir.expr(use_double) else { unreachable!() };
//! assert_eq!(hir.path(p).res, Res::Def(hir.def(hir_lang::Def::Item(f))));
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! [`Resolver`] adds a policy, an [`Env`] for names outside the unit, and a
//! [`Budget`]; [`Program`] resolves several units against each other.
//!
//! ## What resolution guarantees
//!
//! - Every path of the unit ends in exactly one of: resolved (fully, or a
//!   prefix with the rest left to type-directed resolution, as HIR spec
//!   §3.3 allows); resolved with exactly one access diagnostic (private or
//!   protected); `Res::Err` with exactly one diagnostic; or untouched because
//!   it was already resolved (or already an error) on input, or because it is
//!   a bare identifier pattern that binds.
//! - Resolutions are written through `Hir::resolve_partial`, so the result is
//!   a valid `Hir`; a resolution hir-lang refuses becomes `Res::Err` with a
//!   diagnostic instead.
//! - Binders are found with `Hir::lookup_local` and the walk's scope events:
//!   the HIR's scope rules are never re-derived here.
//! - Resolution is deterministic, iterative (no recursion over input), and
//!   bounded: linear in the program apart from glob propagation, inheritance
//!   walks, and suggestions, each capped by the [`Budget`].
//! - The [`Index`] is consistent: every reference's definition lists that
//!   reference, and nothing else.
//!
//! ## `no_std`
//!
//! The crate needs only `alloc`. The default `std` feature is additive.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(unused_must_use)]
#![deny(unused_results)]
#![deny(clippy::unwrap_used)]
#![deny(clippy::expect_used)]
#![deny(clippy::panic)]
#![deny(clippy::todo)]
#![deny(clippy::unimplemented)]
#![deny(clippy::unreachable)]
#![deny(clippy::print_stdout)]
#![deny(clippy::print_stderr)]
#![deny(clippy::dbg_macro)]

extern crate alloc;

mod collect;
mod diag;
mod env;
mod error;
mod imports;
mod index;
mod members;
mod model;
mod pass;
mod policy;
mod program;
mod suggest;

pub use diag::{DiagKind, Diagnostic};
pub use env::{DefKind, Env, Export, MapEnv, NoEnv};
pub use error::{Budget, Limit, ResolveError};
pub use index::{
    DefRef, Definition, Index, Location, Occurrence, Reference, References, RenameSet, SymbolKind,
    Target,
};
pub use policy::{
    Case, ClassScope, Hoist, ItemClass, ModuleScope, Namespace, NsSet, Policy, Redefinition,
    Reexport, RootBinding, Shadowing,
};
pub use program::{ClassMember, Program, Resolution, ResolvedUnit, Resolver};

use hir_lang::Hir;
use intern_lang::Lookup;

/// Resolves one unit with the default (lexical, Kraken-style) policy and no
/// environment: the lazy path.
///
/// `names` is the interner the unit's names were interned in; it is read
/// only to compare spellings for did-you-mean suggestions.
///
/// # Errors
///
/// [`ResolveError::BudgetExceeded`] if the unit exceeds the default
/// [`Budget`]. Name errors in the program are diagnostics in the result, not
/// errors.
///
/// # Examples
///
/// ```
/// use hir_lang::{Builder, Name};
/// use intern_lang::Interner;
///
/// let mut names = Interner::new();
/// let mut b = Builder::new();
/// let lenght = b.name_expr(Name::new(names.intern("lenght")));
/// let body = b.block(&[], Some(lenght));
/// let length = b.func(Name::new(names.intern("length")), &[], body);
/// let root = b.module(None, &[length]);
///
/// let res = resolve_lang::resolve(b.finish(root)?, &names)?;
/// let d = &res.diagnostics()[0];
/// assert_eq!(d.message(&names), "cannot find value `lenght` in this scope; did you mean `length`?");
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn resolve<L: Lookup>(hir: Hir, names: &L) -> Result<Resolution, ResolveError> {
    Resolver::new(Policy::new()).resolve(hir, names)
}

/// Compiles and runs the `rust` code blocks in `README.md` and `docs/API.md` as
/// part of `cargo test`, so the published examples cannot drift from the API.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
#[doc = include_str!("../docs/API.md")]
pub struct MarkdownDocTests;
