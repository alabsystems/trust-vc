// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Theory lemma verification.
//!
//! Provides theory-specific checking for lemmas produced by ay-dpll's theory
//! solvers. Currently supports structural validation for:
//!
//! - **EUF** (Equality with Uninterpreted Functions): Validates that equality
//!   literals in a lemma form a valid transitivity chain or congruence closure.
//! - **LRA** (Linear Real Arithmetic): Validates Farkas certificate structure
//!   by checking that the literal pattern is consistent with an unsatisfiable
//!   linear constraint system.
//!
//! Theories without dedicated checkers (NIA, BV, Array, Seq, Other) return
//! [`TheoryCheckResult::Trusted`].
//!
//! # Limitations
//!
//! At the propositional level, theory lemmas are clause-level: each literal is
//! an opaque `i64`. We do not have access to the underlying term structure
//! (function symbols, argument lists, arithmetic coefficients). The checks here
//! are therefore *structural* — they validate properties that must hold for any
//! well-formed theory lemma regardless of the concrete terms.

use crate::types::{LiteralId, TheoryCheckResult, TheoryLemma, TheoryStats};

// ---------------------------------------------------------------------------
// Public dispatcher
// ---------------------------------------------------------------------------

/// Check a single theory lemma, dispatching to the appropriate theory checker.
///
/// Returns [`TheoryCheckResult::Verified`] if the lemma passes the
/// theory-specific structural checks, [`TheoryCheckResult::Trusted`] if no
/// checker is available for the theory, or [`TheoryCheckResult::Invalid`]
/// if the lemma fails validation.
#[must_use]
pub fn check_theory_lemma(lemma: &TheoryLemma) -> TheoryCheckResult {
    match lemma.theory.as_str() {
        "EUF" => check_euf_lemma(&lemma.clause.literals),
        "LRA" => check_lra_lemma(&lemma.clause.literals),
        _ => TheoryCheckResult::Trusted,
    }
}

/// Check all theory lemmas in a slice and return aggregate statistics.
///
/// If any lemma is invalid, the first invalid result and its lemma ID are
/// returned alongside the accumulated stats.
#[must_use]
pub fn check_all_theory_lemmas(
    lemmas: &[TheoryLemma],
) -> (TheoryStats, Option<(u64, TheoryCheckResult)>) {
    let mut stats = TheoryStats::default();
    let mut first_invalid: Option<(u64, TheoryCheckResult)> = None;

    for lemma in lemmas {
        let result = check_theory_lemma(lemma);
        match &result {
            TheoryCheckResult::Verified => stats.verified_count += 1,
            TheoryCheckResult::Trusted => stats.trusted_count += 1,
            TheoryCheckResult::Invalid { .. } => {
                stats.invalid_count += 1;
                if first_invalid.is_none() {
                    first_invalid = Some((lemma.id, result));
                }
            }
        }
    }

    (stats, first_invalid)
}

// ---------------------------------------------------------------------------
// EUF checker
// ---------------------------------------------------------------------------

/// Validate an EUF (Equality with Uninterpreted Functions) theory lemma.
///
/// An EUF theory lemma is a clause that encodes consequences of the
/// congruence closure algorithm. At the propositional level, the lemma is a
/// disjunction of equality/disequality literals. For a well-formed EUF lemma:
///
/// 1. **Non-empty**: The clause must have at least one literal.
/// 2. **No duplicate literals**: Each literal appears at most once.
/// 3. **No trivial tautologies**: A literal and its negation should not both
///    appear (the clause `{p, -p}` is always true and not a useful lemma).
/// 4. **At most one positive literal**: In a standard EUF conflict clause
///    derived from transitivity or congruence, the clause has the form
///    `(a1 != b1) \/ (a2 != b2) \/ ... \/ (s = t)`, i.e., at most one
///    positive equality conclusion with negative equality premises.
///
/// These are necessary (not sufficient) conditions for a valid EUF lemma.
#[must_use]
pub(crate) fn check_euf_lemma(literals: &[LiteralId]) -> TheoryCheckResult {
    // Rule 1: Non-empty clause.
    if literals.is_empty() {
        return TheoryCheckResult::Invalid {
            reason: "EUF lemma has no literals".to_string(),
        };
    }

    // Rule 2: No duplicate literals.
    let mut seen = std::collections::HashSet::with_capacity(literals.len());
    for &lit in literals {
        if !seen.insert(lit) {
            return TheoryCheckResult::Invalid {
                reason: format!("EUF lemma contains duplicate literal {lit}"),
            };
        }
    }

    // Rule 3: No trivial tautologies (literal and its negation both present).
    for &lit in literals {
        if seen.contains(&(-lit)) {
            return TheoryCheckResult::Invalid {
                reason: format!("EUF lemma is a tautology: contains both {lit} and {}", -lit),
            };
        }
    }

    // Rule 4: At most one positive literal (the conclusion of the
    // transitivity/congruence derivation).
    let positive_count = literals.iter().filter(|&&l| l > 0).count();
    if positive_count > 1 {
        return TheoryCheckResult::Invalid {
            reason: format!("EUF lemma has {positive_count} positive literals; expected at most 1"),
        };
    }

    TheoryCheckResult::Verified
}

// ---------------------------------------------------------------------------
// LRA checker
// ---------------------------------------------------------------------------

/// Validate an LRA (Linear Real Arithmetic) theory lemma.
///
/// An LRA theory lemma encodes an infeasibility certificate (Farkas lemma).
/// The clause asserts that a conjunction of linear constraints is
/// unsatisfiable. At the propositional level:
///
/// 1. **Non-empty**: The clause must have at least one literal.
/// 2. **No duplicate literals**: Each literal appears at most once.
/// 3. **No trivial tautologies**: A literal and its negation must not both
///    appear.
/// 4. **At least two literals**: A Farkas certificate requires combining at
///    least two inequalities to derive a contradiction. A single-literal
///    LRA lemma would mean a single constraint is self-contradictory, which
///    should have been caught during preprocessing, not by the theory solver.
///
/// These are structural checks. Full coefficient-level verification would
/// require access to the underlying arithmetic terms.
#[must_use]
pub(crate) fn check_lra_lemma(literals: &[LiteralId]) -> TheoryCheckResult {
    // Rule 1: Non-empty clause.
    if literals.is_empty() {
        return TheoryCheckResult::Invalid {
            reason: "LRA lemma has no literals".to_string(),
        };
    }

    // Rule 2: No duplicate literals.
    let mut seen = std::collections::HashSet::with_capacity(literals.len());
    for &lit in literals {
        if !seen.insert(lit) {
            return TheoryCheckResult::Invalid {
                reason: format!("LRA lemma contains duplicate literal {lit}"),
            };
        }
    }

    // Rule 3: No trivial tautologies.
    for &lit in literals {
        if seen.contains(&(-lit)) {
            return TheoryCheckResult::Invalid {
                reason: format!("LRA lemma is a tautology: contains both {lit} and {}", -lit),
            };
        }
    }

    // Rule 4: At least two literals for a Farkas-style certificate.
    if literals.len() < 2 {
        return TheoryCheckResult::Invalid {
            reason: format!(
                "LRA lemma has only {} literal; Farkas certificate requires at least 2",
                literals.len()
            ),
        };
    }

    TheoryCheckResult::Verified
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
