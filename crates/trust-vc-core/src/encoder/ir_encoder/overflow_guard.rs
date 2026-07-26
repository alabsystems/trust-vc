//! Overflow check guarding for branching constructs.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Provides `encode_with_overflow_guard` — a structural enforcement pattern
//! ensuring every branching construct correctly guards overflow checks behind
//! branch conditions. Without this, overflow checks from dead branches would
//! cause spurious verification failures.
//!
//! Part of #2236.

use ay_dpll::api::Term;

use crate::encoder::AstExpressionParser;
use crate::error::TrustVcResult;

impl<'a> AstExpressionParser<'a> {
    /// Encode a sub-expression, guarding any overflow checks it emits behind
    /// `skip_cond`: checks are weakened to `skip_cond ∨ check`, so they are
    /// vacuously satisfied when `skip_cond` is true (the branch is not taken).
    ///
    /// All branching constructs (ITE, match, AND/OR, implies) must guard
    /// overflow checks from sub-expressions that only execute conditionally.
    /// Using this helper (or `guard_overflow_checks_since` for post-hoc
    /// guarding) makes the pattern structural rather than manual.
    pub(super) fn encode_with_overflow_guard(
        &mut self,
        skip_cond: Term,
        f: impl FnOnce(&mut Self) -> TrustVcResult<Term>,
    ) -> TrustVcResult<Term> {
        let before = self.overflow_checks.len();
        let result = f(self)?;
        self.guard_overflow_checks_since(before, skip_cond)?;
        Ok(result)
    }

    /// Guard overflow checks added since index `since` with `skip_cond ∨ check`.
    ///
    /// Use this when the closure-based `encode_with_overflow_guard` doesn't fit
    /// (e.g., match arms where `restore_locals` must run between encoding and
    /// error propagation). The semantics are identical.
    ///
    /// Returns `Err` if any `try_or` call fails (e.g., sort mismatch between
    /// the skip condition and a non-Bool overflow predicate). This propagates
    /// into the existing `Unknown` classification path rather than silently
    /// keeping the unguarded predicate. Fixes #2298.
    pub(in crate::encoder) fn guard_overflow_checks_since(
        &mut self,
        since: usize,
        skip_cond: Term,
    ) -> TrustVcResult<()> {
        for check in self.overflow_checks.iter_mut().skip(since) {
            let guarded = self
                .solver
                .try_or(skip_cond, check.1)
                .map_err(|e| format!("failed to guard overflow check '{}': {}", check.0, e))?;
            check.1 = guarded;
        }
        Ok(())
    }

    /// Guards only the overflow checks in `start..end` by `skip_cond`. Unlike
    /// [`Self::guard_overflow_checks_since`], this bounds the END so a later block of
    /// checks (e.g. a match guard's own partiality checks, which must be guarded by a
    /// DIFFERENT condition than the arm body's checks) is left untouched.
    pub(in crate::encoder) fn guard_overflow_checks_range(
        &mut self,
        start: usize,
        end: usize,
        skip_cond: Term,
    ) -> TrustVcResult<()> {
        let end = end.min(self.overflow_checks.len());
        for idx in start..end {
            let cond = self.overflow_checks[idx].1;
            let name = self.overflow_checks[idx].0.clone();
            let guarded = self
                .solver
                .try_or(skip_cond, cond)
                .map_err(|e| format!("failed to guard overflow check '{}': {}", name, e))?;
            self.overflow_checks[idx].1 = guarded;
        }
        Ok(())
    }
}
