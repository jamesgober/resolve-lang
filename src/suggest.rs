//! Did-you-mean: the closest visible name within a small edit distance.
//!
//! The distance is Levenshtein over characters, computed only inside a band
//! of width `2k + 1` around the diagonal (`k` the largest distance worth
//! suggesting), so one comparison costs `O(k · len)`. Every comparison is
//! charged to a run-wide budget of DP cells: once it is spent, diagnostics
//! keep coming but carry no suggestion. Many unresolved names against many
//! visible names therefore cost at most the budget, never their product.

use alloc::vec::Vec;

use hir_lang::Name;
use intern_lang::Lookup;

/// The most candidates one diagnostic considers (after deduplication).
pub(crate) const MAX_CANDIDATES: usize = 4096;

/// The suggestion engine: scratch buffers plus the remaining budget.
pub(crate) struct Suggester {
    cells: u64,
    target: Vec<char>,
    cand: Vec<char>,
    prev: Vec<u32>,
    cur: Vec<u32>,
}

impl Suggester {
    pub(crate) fn new(cells: u64) -> Self {
        Self {
            cells,
            target: Vec::new(),
            cand: Vec::new(),
            prev: Vec::new(),
            cur: Vec::new(),
        }
    }

    /// Whether any budget is left; callers skip collecting candidates when
    /// it is not.
    pub(crate) fn has_budget(&self) -> bool {
        self.cells > 0
    }

    /// The best candidate for `target` among `candidates` (which the caller
    /// has sorted and deduplicated), or `None`.
    ///
    /// Ties go to the smaller distance, then the candidate whose spelling
    /// differs from the target only in ASCII case, then the
    /// lexicographically smaller spelling: deterministic for any input order.
    pub(crate) fn best<L: Lookup>(
        &mut self,
        names: &L,
        target: Name,
        candidates: &[Name],
    ) -> Option<Name> {
        self.target.clear();
        let known = names.resolve_with(target.sym, |s| self.target.extend(s.chars()));
        if known.is_none() || self.target.is_empty() {
            return None;
        }
        let len = self.target.len();
        let k = (len.max(3) / 3).max(1);
        let mut best: Option<(usize, bool, Name)> = None;
        let mut best_text: Vec<char> = Vec::new();
        for &cand in candidates.iter().take(MAX_CANDIDATES) {
            if cand == target || cand.mark != target.mark {
                continue;
            }
            self.cand.clear();
            let Some(()) = names.resolve_with(cand.sym, |s| self.cand.extend(s.chars())) else {
                continue;
            };
            if self.cand.len().abs_diff(len) > k || self.cand.is_empty() {
                continue;
            }
            let cost = (len as u64 + 1).saturating_mul(2 * k as u64 + 1);
            if self.cells < cost {
                self.cells = 0;
                break;
            }
            self.cells -= cost;
            let case_only = self.cand.len() == len
                && self
                    .cand
                    .iter()
                    .zip(&self.target)
                    .all(|(a, b)| a.eq_ignore_ascii_case(b));
            let Some(d) = self.banded(k) else { continue };
            let d = if case_only { 0 } else { d };
            let better = match &best {
                None => true,
                Some((bd, bcase, _)) => {
                    (d, !case_only) < (*bd, !*bcase)
                        || ((d, !case_only) == (*bd, !*bcase) && self.cand < best_text)
                }
            };
            if better {
                best = Some((d, case_only, cand));
                best_text.clear();
                best_text.extend_from_slice(&self.cand);
            }
        }
        best.map(|(_, _, n)| n)
    }

    /// Levenshtein distance between `target` and `cand` if it is at most `k`.
    fn banded(&mut self, k: usize) -> Option<usize> {
        let (a, b) = (&self.target, &self.cand);
        let (la, lb) = (a.len(), b.len());
        let inf = u32::MAX / 2;
        self.prev.clear();
        self.prev.resize(lb + 1, inf);
        self.cur.clear();
        self.cur.resize(lb + 1, inf);
        for (j, slot) in self.prev.iter_mut().enumerate().take(k.min(lb) + 1) {
            *slot = j as u32;
        }
        for i in 1..=la {
            let lo = i.saturating_sub(k).max(1);
            let hi = (i + k).min(lb);
            self.cur.fill(inf);
            if i <= k {
                if let Some(c) = self.cur.get_mut(0) {
                    *c = i as u32;
                }
            }
            let mut row_min = self.cur.first().copied().unwrap_or(inf);
            let ai = a.get(i - 1).copied();
            for j in lo..=hi {
                let sub = u32::from(ai != b.get(j - 1).copied());
                let diag = self.prev.get(j - 1).copied().unwrap_or(inf) + sub;
                let up = self.prev.get(j).copied().unwrap_or(inf) + 1;
                let left = self.cur.get(j - 1).copied().unwrap_or(inf) + 1;
                let v = diag.min(up).min(left);
                if let Some(c) = self.cur.get_mut(j) {
                    *c = v;
                }
                row_min = row_min.min(v);
            }
            if row_min as usize > k {
                return None;
            }
            core::mem::swap(&mut self.prev, &mut self.cur);
        }
        let d = self.prev.get(lb).copied().unwrap_or(inf) as usize;
        (d <= k).then_some(d)
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;
    use alloc::{
        string::{String, ToString},
        vec,
    };
    use intern_lang::Interner;
    use proptest::prelude::*;

    fn full(a: &str, b: &str) -> usize {
        let a: Vec<char> = a.chars().collect();
        let b: Vec<char> = b.chars().collect();
        let mut prev: Vec<usize> = (0..=b.len()).collect();
        for i in 1..=a.len() {
            let mut cur = vec![i; b.len() + 1];
            for j in 1..=b.len() {
                let sub = usize::from(a[i - 1] != b[j - 1]);
                cur[j] = (prev[j - 1] + sub).min(prev[j] + 1).min(cur[j - 1] + 1);
            }
            prev = cur;
        }
        prev[b.len()]
    }

    fn pick(target: &str, cands: &[&str]) -> Option<String> {
        let mut names = Interner::new();
        let t = Name::new(names.intern(target));
        let mut c: Vec<Name> = cands.iter().map(|s| Name::new(names.intern(s))).collect();
        c.sort();
        c.dedup();
        let mut s = Suggester::new(u64::MAX);
        s.best(&names, t, &c)
            .map(|n| names.resolve(n.sym).unwrap().to_string())
    }

    #[test]
    fn test_best_picks_closest() {
        assert_eq!(
            pick("lenght", &["length", "width", "len"]).as_deref(),
            Some("length")
        );
        assert_eq!(pick("foo", &["bar", "baz"]), None);
        assert_eq!(pick("x", &["y"]).as_deref(), Some("y"));
        assert_eq!(pick("Count", &["count", "cont"]).as_deref(), Some("count"));
    }

    #[test]
    fn test_best_ties_break_alphabetically() {
        assert_eq!(pick("cat", &["cot", "bat", "cut"]).as_deref(), Some("bat"));
    }

    #[test]
    fn test_exhausted_budget_suggests_nothing() {
        let mut names = Interner::new();
        let t = Name::new(names.intern("lenght"));
        let c = [Name::new(names.intern("length"))];
        let mut s = Suggester::new(3);
        assert_eq!(s.best(&names, t, &c), None);
        assert!(!s.has_budget());
    }

    proptest! {
        #[test]
        fn prop_banded_matches_full_dp(a in "[a-c]{0,9}", b in "[a-c]{0,9}") {
            let mut s = Suggester::new(u64::MAX);
            s.target = a.chars().collect();
            s.cand = b.chars().collect();
            let k = 3;
            let d = full(&a, &b);
            let banded = s.banded(k);
            if d <= k {
                prop_assert_eq!(banded, Some(d));
            } else {
                prop_assert_eq!(banded, None);
            }
        }
    }
}
