//! Errors that stop a resolution run, and the budgets that bound one.

use core::fmt;

use hir_lang::UnitId;

/// Which budget a run exhausted.
///
/// # Examples
///
/// ```
/// use resolve_lang::Limit;
///
/// assert_eq!(Limit::GlobBindings.name(), "glob bindings");
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Limit {
    /// Names copied into scopes by glob imports (each glob edge times each
    /// name it carries).
    GlobBindings,
    /// Steps spent walking inheritance chains for `self::`, `parent::`, and
    /// `Class::member` lookups, and access checks over class hierarchies.
    MemberSteps,
}

impl Limit {
    /// A short name, for messages.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Limit;
    ///
    /// assert_eq!(Limit::MemberSteps.name(), "member lookup steps");
    /// ```
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::GlobBindings => "glob bindings",
            Self::MemberSteps => "member lookup steps",
        }
    }
}

/// Why a resolution run stopped without a result.
///
/// Name errors in the program are not `ResolveError`s: they are
/// [`Diagnostic`](crate::Diagnostic)s in a successful result. A run fails only
/// when the input is unusable as a whole or exceeds a [`Budget`].
///
/// # Examples
///
/// ```
/// use hir_lang::UnitId;
/// use resolve_lang::ResolveError;
///
/// let e = ResolveError::DuplicateUnit { unit: UnitId::new(3) };
/// assert_eq!(e.to_string(), "two units of the program have the id 3");
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ResolveError {
    /// The program reached a budget limit. Raise the limit with
    /// [`Budget`] if the input is trusted, or reject the input.
    BudgetExceeded {
        /// The limit reached.
        limit: Limit,
    },
    /// Two units share a [`UnitId`]; `DefId`s could not tell them apart.
    /// Give every unit of a program a distinct id.
    DuplicateUnit {
        /// The shared id.
        unit: UnitId,
    },
}

impl fmt::Display for ResolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BudgetExceeded { limit } => {
                write!(f, "resolution exceeded its budget of {}", limit.name())
            }
            Self::DuplicateUnit { unit } => {
                write!(f, "two units of the program have the id {}", unit.as_u32())
            }
        }
    }
}

impl core::error::Error for ResolveError {}

/// Explicit limits on the work untrusted input can cause.
///
/// The resolver is linear in the size of the program except in three places,
/// each bounded here: glob imports (each glob edge carries every name of its
/// target), inheritance walks for member lookups, and did-you-mean
/// comparisons. Exceeding the first two fails the run with
/// [`ResolveError::BudgetExceeded`]; exhausting the suggestion budget only
/// stops suggestions.
///
/// # Examples
///
/// ```
/// use resolve_lang::Budget;
///
/// let b = Budget::default().with_glob_bindings(1_000);
/// assert_eq!(b.glob_bindings(), 1_000);
/// assert!(Budget::unlimited().suggestion_cells() > b.suggestion_cells());
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Budget {
    glob_bindings: u64,
    member_steps: u64,
    suggestion_cells: u64,
}

impl Default for Budget {
    /// 16 million glob bindings, 16 million member steps, 32 million
    /// suggestion cells: far beyond real programs, small enough to bound a
    /// hostile one to well under a second of work each.
    fn default() -> Self {
        Self {
            glob_bindings: 16_000_000,
            member_steps: 16_000_000,
            suggestion_cells: 32_000_000,
        }
    }
}

impl Budget {
    /// No limits (for trusted input).
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Budget;
    ///
    /// assert_eq!(Budget::unlimited().member_steps(), u64::MAX);
    /// ```
    #[must_use]
    pub const fn unlimited() -> Self {
        Self {
            glob_bindings: u64::MAX,
            member_steps: u64::MAX,
            suggestion_cells: u64::MAX,
        }
    }

    /// Sets the glob-binding limit.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Budget;
    ///
    /// assert_eq!(Budget::default().with_glob_bindings(5).glob_bindings(), 5);
    /// ```
    #[must_use]
    pub const fn with_glob_bindings(mut self, n: u64) -> Self {
        self.glob_bindings = n;
        self
    }

    /// Sets the member-lookup step limit.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Budget;
    ///
    /// assert_eq!(Budget::default().with_member_steps(5).member_steps(), 5);
    /// ```
    #[must_use]
    pub const fn with_member_steps(mut self, n: u64) -> Self {
        self.member_steps = n;
        self
    }

    /// Sets the did-you-mean budget, in edit-distance table cells.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Budget;
    ///
    /// assert_eq!(Budget::default().with_suggestion_cells(0).suggestion_cells(), 0);
    /// ```
    #[must_use]
    pub const fn with_suggestion_cells(mut self, n: u64) -> Self {
        self.suggestion_cells = n;
        self
    }

    /// The glob-binding limit.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Budget;
    ///
    /// assert_eq!(Budget::default().glob_bindings(), 16_000_000);
    /// ```
    #[must_use]
    pub const fn glob_bindings(&self) -> u64 {
        self.glob_bindings
    }

    /// The member-lookup step limit.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Budget;
    ///
    /// assert_eq!(Budget::default().member_steps(), 16_000_000);
    /// ```
    #[must_use]
    pub const fn member_steps(&self) -> u64 {
        self.member_steps
    }

    /// The did-you-mean budget.
    ///
    /// # Examples
    ///
    /// ```
    /// use resolve_lang::Budget;
    ///
    /// assert_eq!(Budget::default().suggestion_cells(), 32_000_000);
    /// ```
    #[must_use]
    pub const fn suggestion_cells(&self) -> u64 {
        self.suggestion_cells
    }
}
