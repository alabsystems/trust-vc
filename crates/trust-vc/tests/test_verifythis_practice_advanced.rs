// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026 practice — advanced tiers (6-9)
//!
//! Split from `test_verifythis_practice.rs` (#2319) to stay under the
//! commit-hook size limit.
//!
//! - Tier 6: Quantified properties via macro
//! - Tier 7: u64 quantifier types
//! - Tier 8: Seq + quantifier (competition pattern)
//! - Tier 9: Proc-macro competition workflow
//!
//! Issue #2187: VerifyThis 2026 competition readiness assessment
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline

mod common;

use trust_vc_core::vc::{ObligationKind, VerificationContext};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::{UnknownCategory, VerifyResult};

// ========================================================================
// TIER 6: Quantified properties via macro (NEW CAPABILITY)
// ay-dpll now handles quantified formulas — test VerifyThis patterns.
// ========================================================================

/// Test forall with implication — the core VerifyThis invariant pattern.
/// "For all j < n, a[j] <= max" is the invariant of every max-finding loop.
#[test]
fn test_vt_tier6_quantified_implication() {
    common::with_clean_verification(|| {
        // Test: forall x: i32. x > 5 => x > 0
        // Encoded as: forall x. !(x > 5) || (x > 0)
        #[allow(clippy::nonminimal_bool)]
        let _ = trust_vc::forall!(|x: i32| !(x > 5) || x > 0);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Encoder-level Skolemization (#2187): trigger-less forall assertions
        // produce ground formulas (no ay quantifier). Verification-by-refutation
        // checks UNSAT of the negation directly, no CEGQI needed.
        assert!(
            matches!(result, VerifyResult::Verified),
            "TIER 6 PASS: quantified implication should verify with Skolemization, got: {:?}",
            result,
        );
    })
}

/// Test quantified property with free variables (simulating array elements).
/// "Given a0 < a1 < a2, forall x: if x == a0 || x == a1 || x == a2, then x <= a2"
#[test]
fn test_vt_tier6_quantified_array_bound() {
    common::with_clean_verification(|| {
        verify_macro::collect_variable("a0".to_string(), "i32".to_string());
        verify_macro::collect_variable("a1".to_string(), "i32".to_string());
        verify_macro::collect_variable("a2".to_string(), "i32".to_string());

        // Assume sorted order
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "sorted".to_string(),
            "a0 <= a1 && a1 <= a2".to_string(),
            None,
        );

        // Assert: a2 is the max (all elements <= a2)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "a2_is_max".to_string(),
            "a0 <= a2 && a1 <= a2".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "TIER 6 PASS: sorted array max should verify, got: {:?}",
            result,
        );
    })
}

/// Test ITE encoding with disjunction — ay-dpll now handles this pattern.
/// The disjunctive `(cond && x) || (!cond && y)` max encoding verifies
/// reliably, so this is now a strict Verified gate.
#[test]
fn test_vt_tier6_ite_disjunction() {
    common::with_clean_verification(|| {
        verify_macro::collect_variable("a".to_string(), "i32".to_string());
        verify_macro::collect_variable("b".to_string(), "i32".to_string());
        verify_macro::collect_variable("m".to_string(), "i32".to_string());

        // ITE pattern: m = if a >= b then a else b
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "ite_max".to_string(),
            "(a >= b && m == a) || (a < b && m == b)".to_string(),
            None,
        );

        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "m_ge_a".to_string(),
            "m >= a".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "TIER 6 PASS: ITE disjunction max should verify, got: {:?}",
            result,
        );
    })
}

// ========================================================================
// TIER 7: u64 quantifier types (FIXED — was blocking VerifyThis u64 patterns)
// VerifyThis uses usize/u64 loop counters in quantified invariants.
// ========================================================================

/// u64 forall tautology — validates the type propagation fix.
/// Previously errored with "type mismatch: IR declared Int{32}" because
/// lookup_var_type fell back to Int{32} for quantifier-bound variables.
#[test]
fn test_vt_tier7_u64_quantifier_tautology() {
    common::with_clean_verification(|| {
        let _ = trust_vc::forall!(|x: u64| x == x);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "TIER 7 PASS: u64 forall tautology should verify, got: {:?}",
            result,
        );
    })
}

/// u64 exists tautology — validates the typed exists path verifies cleanly.
///
/// `exists x: u64. x == x` is valid, so once typed existential support is
/// wired through correctly this should verify rather than regressing back to
/// the old sort mismatch or fail-closed `Unknown`.
#[test]
fn test_vt_tier7_u64_exists() {
    common::with_clean_verification(|| {
        let _ = trust_vc::exists!(|x: u64| x == x);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "TIER 7 PASS: u64 exists tautology should verify, got: {:?}",
            result,
        );
    })
}

/// Multi-type quantifier: u32 and u64 bound variables in the same forall.
/// This tests that the registration handles multiple variables correctly.
#[test]
fn test_vt_tier7_multi_type_quantifier() {
    common::with_clean_verification(|| {
        #[allow(unused_variables)]
        let _ = trust_vc::forall!(|i: u32, j: u64| i == i);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "TIER 7 PASS: multi-type forall tautology should verify, got: {:?}",
            result,
        );
    })
}

// ========================================================================
// TIER 8: Seq + quantifier — the VerifyThis competition pattern
// Real competition problems use quantified invariants over sequences.
// These tests use VerificationContext directly (programmatic API).
//
// BV-sorted skolemization keeps the Seq+forall path in decidable QF_ABV for
// these core patterns, so keep this tier strict to catch regressions.
// ========================================================================

/// VerifyThis core pattern: "forall j < n. s[j] >= 0" over a Seq.
/// This is the exact pattern needed for loop invariant verification.
#[test]
fn test_vt_tier8_seq_forall_all_nonneg() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("elem0", "s.index(0) == 10");
    ctx.push_assume("elem1", "s.index(1) == 20");
    ctx.push_assume("elem2", "s.index(2) == 30");
    ctx.push_assert("all_nonneg", "forall(|i: u64| !(i < 3) || s.index(i) >= 0)");

    let result = ctx.verify();
    // BV-sorted Skolemization (#2187): bound vars use Sort::BitVec instead of
    // Sort::Int, avoiding int2bv that ay-dpll cannot decide. This makes the
    // formula ground BV — fully decidable.
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 8 PASS: Seq forall all-nonneg should verify with BV Skolemization, got: {:?}",
        result,
    );
}

/// Negative: Seq with negative element — forall-nonneg must NOT verify.
/// This remains a strict soundness gate for the skolemized sequence path.
#[test]
fn test_vt_tier8_seq_forall_negative_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.push_assume("len", "s.len() == 2");
    ctx.push_assume("elem0", "s.index(0) == 10");
    ctx.push_assume("elem1", "s.index(1) == -5");
    ctx.push_assert(
        "all_nonneg_false",
        "forall(|i: u64| !(i < 2) || s.index(i) >= 0)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 8 NEGATIVE: Seq with negative elem should produce Counterexample, got: {:?}",
        result,
    );
}

/// Max-element proof: given sorted Seq, last element is max.
/// Pattern: assume sorted => assert forall j. s[j] <= s[n-1]
#[test]
fn test_vt_tier8_seq_max_element_proof() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("sorted01", "s.index(0) <= s.index(1)");
    ctx.push_assume("sorted12", "s.index(1) <= s.index(2)");
    ctx.push_assert(
        "all_le_max",
        "forall(|j: u64| !(j < 3) || s.index(j) <= s.index(2))",
    );

    let result = ctx.verify();
    // BV-sorted Skolemization (#2187): ground BV formula, fully decidable.
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 8 PASS: sorted Seq max-element should verify with BV Skolemization, got: {:?}",
        result,
    );
}

// ========================================================================
// TIER 9: Proc-macro competition workflow
// Real competition entries use #[trust_vc::proof] instead of building
// VerificationContext by hand. These tests keep that user-facing proc-macro
// bridge covered with a competition-style interval-shrink VC.
// ========================================================================

/// Binary-search right branch shrinks the search interval on concrete traces.
///
/// Competition-safe decomposition: prove the arithmetic on fixed traces
/// through the proc-macro bridge instead of relying on symbolic loop-state
/// assumptions inside a proof function.
#[test]
fn test_vt_tier9_proc_macro_binary_search_right_branch_shrinks() {
    let result = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn binary_search_right_branch_shrinks() {
            trust_vc::assert!(8_u64 - (4_u64 + 1) < 8_u64 - 0_u64);
            trust_vc::assert!(9_u64 - (7_u64 + 1) < 9_u64 - 5_u64);
            trust_vc::assert!(3_u64 - (2_u64 + 1) < 3_u64 - 2_u64);
        }

        binary_search_right_branch_shrinks();
    });

    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 9 PASS: proc-macro binary-search right branch should verify, got: {:?}",
        result,
    );
}

/// Off-by-one binary-search update must be rejected on the proc-macro path.
///
/// When `mid == lo`, the mistaken width formula `hi - mid < hi - lo` becomes
/// `4 < 4`, which is false. The current proc-macro bridge still routes this
/// concrete negative through a fail-closed `Unknown`, so the stable contract
/// here is "must not verify" rather than "must always produce Counterexample".
#[test]
fn test_vt_tier9_proc_macro_binary_search_off_by_one_rejected() {
    let result = common::verify_should_fail(|| {
        #[trust_vc::proof]
        fn binary_search_right_branch_wrong_width() {
            trust_vc::assert!(4_u64 < 4_u64);
        }

        binary_search_right_branch_wrong_width();
    });

    assert!(
        matches!(
            &result,
            VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
        ),
        "TIER 9 NEGATIVE: proc-macro off-by-one width update must not verify, got: {:?}",
        result,
    );
    if matches!(&result, VerifyResult::Unknown { .. }) {
        assert_eq!(
            result.unknown_category(),
            Some(UnknownCategory::SolverUnknown),
            "TIER 9 NEGATIVE: proc-macro off-by-one width Unknown should stay classified as a solver limitation, got: {:?}",
            result,
        );
    }
}
