//! Strategic audit tests — P1-482 iteration findings.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Findings from Prover strategic audit of assertion.rs, typed.rs,
//! unknown_category.rs, and rewrite.rs. Each test targets a specific
//! implicit invariant or gap discovered during the audit.
//!
//! Test categories:
//! 1. Multi-predicate overflow push/pop isolation
//! 2. Non-default solver mode abort-all behavior
//! 3. UnknownCategory structured vs string classification consistency

use super::*;

// ========================================================================
// 1. Multi-predicate overflow push/pop isolation
//
// check_overflow_predicates (assertion.rs:510-660) iterates multiple
// overflow predicates using SolverScope push/pop on the SAME encoder.
// ay-dpll push/pop can corrupt solver state for subsequent queries.
// The main assertion uses a fresh encoder (line 217), but overflow
// predicates share one encoder. These tests verify the second predicate
// is correctly checked despite prior push/pop cycles.
// ========================================================================

/// DISCRIMINATING: Two overflow operations — first passes, second fails.
///
/// Expression: `(x + y) * z == (x + y) * z` (tautological) with overflow checks.
/// Setup: x=10, y=20, z unconstrained.
/// - add overflow for x + y: 10 + 20 = 30, no overflow → passes
/// - mul overflow for (x + y) * z: 30 * z can overflow when z is large
///
/// The assertion is TAUTOLOGICAL so it would Verify without overflow checks.
/// With overflow checks, the second predicate (mul overflow) must be caught.
///
/// If push/pop corrupts the solver between the first and second overflow
/// check, the second check could falsely pass (Unsat instead of Sat),
/// and the tautological assertion would verify — a false positive.
#[test]
fn test_multi_overflow_predicate_second_detected() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("z", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 20"));
    // z is unconstrained — solver can pick z such that 30 * z overflows
    // Tautological assertion: only overflow checks can reject this
    ctx.push_obligation(ProofObligation::assert(
        "product_taut",
        "(x + y) * z == (x + y) * z",
    ));

    let result = AYEncoder::verify(&ctx);
    // Must NOT verify — overflow detection should catch unconstrained z
    // in (x + y) * z. If this verifies, the second overflow predicate
    // was missed (push/pop isolation failure).
    expect_fail_closed(&result, "Tautological (x + y) * z with unconstrained z must NOT verify — mul overflow predicate isolation");
}

/// CONTROL: Same expression with z constrained to prevent overflow → verifies.
///
/// If both overflow predicates pass (x + y and (x + y) * z are safe),
/// the main assertion should verify normally. This control ensures the
/// test above is not failing for unrelated reasons.
#[test]
fn test_multi_overflow_predicate_both_pass_then_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("z", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 20"));
    ctx.push_obligation(ProofObligation::assume("z_small", "z == 2"));
    // (10 + 20) * 2 = 60 — no overflow, result > 0
    ctx.push_obligation(ProofObligation::assert("product_pos", "(x + y) * z > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "(10 + 20) * 2 = 60 > 0 should verify with no overflow",
    );
}

/// DISCRIMINATING: Three chained overflow operations with tautological assertion.
///
/// Expression: `(a + b) + (a + b) == (a + b) + (a + b)` (tautological).
/// Setup: a = 1073741823, b = 1073741823 (both just under i32::MAX/2).
/// - a + b = 2147483646, no signed overflow (just under i32::MAX)
/// - (a + b) + (a + b) = 4294967292, OVERFLOWS i32
///
/// The assertion is tautological and would verify without overflow checks.
/// The third overflow predicate (outer addition) must be detected despite
/// two prior push/pop cycles on the same solver.
#[test]
fn test_triple_overflow_predicate_chain() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // a = (i32::MAX - 1) / 2, b = same
    // a + b = 2147483646, no overflow (1 under i32::MAX)
    // (a + b) + (a + b) = 4294967292, overflows i32 (> 2147483647)
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1073741823"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1073741823"));
    // Tautological assertion — only overflow checks can reject this
    ctx.push_obligation(ProofObligation::assert(
        "chain_taut",
        "(a + b) + (a + b) == (a + b) + (a + b)",
    ));

    let result = AYEncoder::verify(&ctx);
    // The outer addition overflows i32 — must NOT verify
    expect_fail_closed(&result, "Tautological chained addition with overflow must NOT verify — (a + b) + (a + b) overflows i32");
}

// ========================================================================
// 2. Solver mode dispatch behavior
//
// NonlinearArith and BitVector modes now route through the normal
// verification path (ay's Logic::All handles NIA and BV natively).
// Compute mode now does const evaluation. Part of #2405.
// ========================================================================

/// Compute mode with unresolved symbolic variable returns Unknown before
/// reaching later assertions. No assumption provides a binding for x,
/// so compute mode fails closed. Part of #2454 (updated from #2405).
#[test]
fn test_compute_mode_aborts_remaining_assertions() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // No assumption binding x — compute mode cannot resolve.

    // First obligation: Compute mode — symbolic x cannot be const-evaluated
    let compute = crate::vc::ProofObligation::new(
        "compute_check".to_string(),
        "x == 5".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(compute);

    // Second obligation: would error if reached
    ctx.push_obligation(ProofObligation::assert("later_invalid", "x / 0 == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_unknown(&result, "Compute mode should abort-all and return Unknown");
}

/// A failing default-mode assertion before a Compute-mode one still
/// surfaces as Counterexample — the first assertion fails before we
/// reach the unsupported mode.
#[test]
fn test_default_mode_failure_preempts_later_compute_abort() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));

    // First: Default mode, definitely false when x == 5
    ctx.push_obligation(ProofObligation::assert("failing_first", "x < 0"));

    // Second: Compute mode — symbolic x returns Unknown
    let compute = crate::vc::ProofObligation::new(
        "compute_check".to_string(),
        "x == 5".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Compute);
    ctx.obligations.push(compute);

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "A failing default assertion before Compute mode must surface as Counterexample before the later mode check aborts");
}

// ========================================================================
// 3. UnknownCategory classification consistency
//
// unknown_category.rs has two classification paths:
// - from_unknown_reason(): structured UnknownReason → UnknownCategory
// - classify(): string reason → UnknownCategory
//
// These paths must be consistent: a Timeout UnknownReason should produce
// the same UnknownCategory as a string containing "timed out".
// ========================================================================

/// DISCRIMINATING: Structured Timeout maps to the same category as
/// string "timed out". If the string path drifts, retry logic
/// (which uses is_retriable()) could silently stop working.
#[test]
fn test_unknown_category_timeout_paths_consistent() {
    use crate::encoder::verification::unknown_category::UnknownCategory;
    use ay_dpll::UnknownReason;

    let structured = UnknownCategory::from_unknown_reason(Some(UnknownReason::Timeout));
    let string_based = UnknownCategory::classify(
        "Solver timed out after 10s for 'test' (BV solver timeout enforcement, #1605)",
    );

    assert_eq!(
        structured,
        Some(string_based),
        "Structured Timeout and string 'timed out' must produce same category"
    );
    assert!(
        string_based.is_retriable(),
        "Timeout category must be retriable"
    );
}

/// DISCRIMINATING: ResourceLimit is classified as SolverUnknown (not retriable).
///
/// This documents the current design: ResourceLimit is NOT retriable.
/// If this becomes retriable in the future (design change), update this test.
/// The concern is that ResourceLimit-induced Unknowns could benefit from
/// retry with extended timeout, but currently they do not get retried.
#[test]
fn test_resource_limit_not_retriable_by_design() {
    use crate::encoder::verification::unknown_category::UnknownCategory;
    use ay_dpll::UnknownReason;

    let category =
        UnknownCategory::from_unknown_reason(Some(UnknownReason::ResourceLimit)).unwrap();
    assert_eq!(
        category,
        UnknownCategory::SolverUnknown,
        "ResourceLimit should classify as SolverUnknown"
    );
    assert!(
        !category.is_retriable(),
        "ResourceLimit is NOT retriable by current design — \
         if this changes, update retry logic in assertion.rs to also \
         retry SolverUnknown results. See P1-482 strategic audit."
    );
}

/// DISCRIMINATING: QuantifierRoundLimit is classified as SolverUnknown.
///
/// Documents that quantifier incompleteness is not retriable.
/// Extended timeout would not help if the quantifier instantiation
/// round limit is reached (it's a depth limit, not a time limit).
#[test]
fn test_quantifier_round_limit_not_retriable_by_design() {
    use crate::encoder::verification::unknown_category::UnknownCategory;
    use ay_dpll::UnknownReason;

    let category =
        UnknownCategory::from_unknown_reason(Some(UnknownReason::QuantifierRoundLimit)).unwrap();
    assert_eq!(
        category,
        UnknownCategory::SolverUnknown,
        "QuantifierRoundLimit should classify as SolverUnknown"
    );
    assert!(
        !category.is_retriable(),
        "QuantifierRoundLimit is NOT retriable — it's a depth limit, not timeout"
    );
}

/// DISCRIMINATING: Interrupted maps to SolverUnknown, not Timeout.
///
/// An interrupted solve (via interrupt handle) should NOT be retried.
/// The interrupt is intentional (timeout enforcement) and retrying would
/// produce the same result.
#[test]
fn test_interrupted_not_retriable() {
    use crate::encoder::verification::unknown_category::UnknownCategory;
    use ay_dpll::UnknownReason;

    let category = UnknownCategory::from_unknown_reason(Some(UnknownReason::Interrupted)).unwrap();
    assert_eq!(
        category,
        UnknownCategory::SolverUnknown,
        "Interrupted should classify as SolverUnknown, not Timeout"
    );
    assert!(
        !category.is_retriable(),
        "Interrupted solves should NOT be retried"
    );
}

/// EXHAUSTIVENESS: Every UnknownReason variant maps to a known category.
///
/// Tests all explicitly listed variants in from_unknown_reason to ensure
/// the wildcard arm only catches genuinely new variants. If a new variant
/// is added to ay-dpll, this test should be updated to handle it explicitly.
#[test]
fn test_from_unknown_reason_all_known_variants_classified() {
    use crate::encoder::verification::unknown_category::UnknownCategory;
    use ay_dpll::UnknownReason;

    // Resource/budget reasons stay SolverUnknown (non-failure Unknown); genuine
    // theory-incompleteness reasons now map to Incompleteness (model-less
    // failure on a proof obligation). See design-unknown-as-failure.md.
    let known_variants = vec![
        (UnknownReason::Timeout, UnknownCategory::Timeout),
        (UnknownReason::ResourceLimit, UnknownCategory::SolverUnknown),
        (UnknownReason::MemoryLimit, UnknownCategory::SolverUnknown),
        (UnknownReason::Interrupted, UnknownCategory::SolverUnknown),
        (UnknownReason::Incomplete, UnknownCategory::Incompleteness),
        (
            UnknownReason::QuantifierRoundLimit,
            UnknownCategory::SolverUnknown,
        ),
        (
            UnknownReason::QuantifierDeferred,
            UnknownCategory::SolverUnknown,
        ),
        (
            UnknownReason::QuantifierUnhandled,
            UnknownCategory::Incompleteness,
        ),
        (
            UnknownReason::QuantifierCegqiIncomplete,
            UnknownCategory::Incompleteness,
        ),
        (
            UnknownReason::QuantifierEmatchingExistsIncomplete,
            UnknownCategory::Incompleteness,
        ),
        (UnknownReason::SplitLimit, UnknownCategory::SolverUnknown),
        (
            UnknownReason::ExpressionSplit,
            UnknownCategory::Incompleteness,
        ),
        (UnknownReason::Unsupported, UnknownCategory::Incompleteness),
        (
            UnknownReason::UnsupportedArithmetic,
            UnknownCategory::Incompleteness,
        ),
        (
            UnknownReason::UnsupportedMixedCollection,
            UnknownCategory::Incompleteness,
        ),
        (UnknownReason::InternalError, UnknownCategory::SolverUnknown),
        (UnknownReason::ProofTrusted, UnknownCategory::SolverUnknown),
        (UnknownReason::Unknown, UnknownCategory::SolverUnknown),
    ];

    for (reason, expected) in known_variants {
        let actual = UnknownCategory::from_unknown_reason(Some(reason)).unwrap();
        assert_eq!(
            actual, expected,
            "UnknownReason::{:?} should map to {:?}, got {:?}",
            reason, expected, actual,
        );
    }
}

/// SolverPanic is a solver limitation but NOT soundness-relevant.
///
/// Documents the design decision: a ay-dpll panic caught by catch_unwind
/// is classified as a solver limitation (not a trust_vc bug) and not
/// soundness-relevant (it doesn't indicate the assertion is invalid).
///
/// Concern: a solver panic could mask a real counterexample (the solver
/// crashes while trying to prove Sat). This test documents the current
/// classification for future review.
#[test]
fn test_solver_panic_classification_documented() {
    use crate::encoder::verification::unknown_category::UnknownCategory;

    let category = UnknownCategory::SolverPanic;
    assert!(
        category.is_solver_limitation(),
        "SolverPanic should be a solver limitation"
    );
    assert!(
        !category.is_soundness_relevant(),
        "SolverPanic is NOT soundness-relevant by design — \
         a ay crash could mask a Sat result (real counterexample), \
         but we treat it conservatively as Unknown. See P1-482 audit."
    );
}
