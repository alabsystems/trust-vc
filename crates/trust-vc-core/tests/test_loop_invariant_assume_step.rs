//! Tests for the loop invariant ASSUME step: after verification, the invariant
//! is added as an assumption for subsequent obligations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! ## Background
//!
//! The encoder processes LoopInvariant obligations in two phases:
//! 1. **Base case**: verify invariant holds from existing assumptions
//! 2. **Inductive step**: verify invariant is preserved (havoc-all or frame condition)
//!
//! If both pass, the invariant is ASSUMED for subsequent obligations
//! (typed.rs: `verified_invariant_obligations.push(invariant)`).
//!
//! ## Flat-scope limitation (#1631)
//!
//! In the current flat-scope architecture, ALL assumptions (preconditions,
//! verified invariants) are globally visible to ALL obligations. This makes
//! the assume step logically redundant:
//!
//! - Base case proof: preconditions → invariant
//! - Therefore: preconditions → (anything derivable from invariant)
//! - The assume step adds no information beyond what preconditions provide
//!
//! Proper discrimination requires loop body scoping (#1609) where:
//! - Preconditions are NOT visible inside the loop body
//! - Only the invariant assumption is available for intra-loop assertions
//!
//! ## What these tests cover
//!
//! 1. NEGATIVE: Failed invariants are correctly reported (not masked by assertions)
//! 2. CASCADING: Invariant chains exercise the assume mechanism
//! 3. REDUNDANCY: Explicit demonstration of flat-scope limitation
//! 4. FRAME CONDITION: Assume step interaction with frame-condition mode
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests invoke ay verification through `VerificationContext::verify()`.

use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

mod common;

// ============================================================
// NEGATIVE: Failed invariant is NOT assumed
// ============================================================

/// DISCRIMINATING: Failed invariant base case reports invariant, not assertion.
///
/// If the encoder incorrectly assumed a failed invariant, the assertion
/// `x > 0` might pass (from the incorrectly assumed invariant). Instead,
/// the encoder should report the invariant base case failure and never
/// reach the assertion.
///
/// Discrimination: if the assume step incorrectly assumed UNVERIFIED
/// invariants, the result would be Verified instead of Counterexample,
/// or the counterexample would name the assertion instead of the invariant.
#[test]
fn test_failed_invariant_not_assumed_for_assertion() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // NO preconditions — x is unconstrained

        // Loop invariant: x > 0 (base case FAILS for unconstrained x)
        ctx.push_obligation(ProofObligation::loop_invariant("inv_x_pos", "x > 0"));

        // Assertion: x > 0 (would pass if invariant were incorrectly assumed)
        ctx.push_obligation(ProofObligation::assert("post_x_pos", "x > 0"));

        let result = ctx.verify();

        // Must fail at the invariant, not reach the assertion
        match &result {
            VerifyResult::Counterexample {
                obligation_name, ..
            } => {
                assert!(
                    obligation_name.contains("inv_x_pos"),
                    "Counterexample should name the invariant 'inv_x_pos', got: {}",
                    obligation_name
                );
                assert!(
                    !obligation_name.contains("post_x_pos"),
                    "Counterexample should NOT name the assertion 'post_x_pos', got: {}",
                    obligation_name
                );
            }
            other => panic!(
                "Expected Counterexample at invariant base case, got: {:?}",
                other
            ),
        }
    })
}

/// DISCRIMINATING: Failed inductive step reports invariant, not later assertion.
///
/// The invariant `x > 0` passes base case (from precondition) but fails
/// the havoc-all inductive step (not a tautology for i32). The encoder
/// should report the inductive step failure and not reach the assertion.
#[test]
fn test_failed_inductive_step_not_assumed_for_assertion() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        ctx.push_obligation(ProofObligation::assume("precond", "x > 0"));

        // Invariant: x > 0 (base case passes, inductive step fails)
        ctx.push_obligation(ProofObligation::loop_invariant("inv_x_pos", "x > 0"));

        // Assertion: x >= 1 (would pass if invariant were assumed)
        ctx.push_obligation(ProofObligation::assert("post_assertion", "x >= 1"));

        let result = ctx.verify();

        match &result {
            VerifyResult::Counterexample {
                obligation_name, ..
            } => {
                assert!(
                    obligation_name.contains("inv_x_pos")
                        && obligation_name.contains("inductive step"),
                    "Should fail at inductive step of 'inv_x_pos', got: {}",
                    obligation_name
                );
            }
            other => panic!(
                "Expected Counterexample at inductive step, got: {:?}",
                other
            ),
        }
    })
}

/// DISCRIMINATING: First invariant fails, second invariant is never checked.
///
/// If the encoder incorrectly continued past a failed first invariant and
/// assumed it, the second invariant's base case might pass from the
/// (incorrectly) assumed first invariant. Instead, verification should
/// stop at the first invariant's failure.
#[test]
fn test_failed_first_invariant_blocks_second() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("y", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // NO preconditions

        // Invariant 1: x > 0 (base case FAILS)
        ctx.push_obligation(ProofObligation::loop_invariant("inv_1_x", "x > 0"));

        // Invariant 2: y > 0 (would also fail, but should never be reached)
        ctx.push_obligation(ProofObligation::loop_invariant("inv_2_y", "y > 0"));

        // Assertion (should never be reached)
        ctx.push_obligation(ProofObligation::assert("post", "x > 0 && y > 0"));

        let result = ctx.verify();

        match &result {
            VerifyResult::Counterexample {
                obligation_name, ..
            } => {
                assert!(
                    obligation_name.contains("inv_1_x"),
                    "Should fail at first invariant 'inv_1_x', got: {}",
                    obligation_name
                );
                assert!(
                    !obligation_name.contains("inv_2_y"),
                    "Should NOT reach second invariant 'inv_2_y', got: {}",
                    obligation_name
                );
            }
            other => panic!("Expected Counterexample at inv_1_x, got: {:?}", other),
        }
    })
}

// ============================================================
// CASCADING: Invariant chain exercises assume mechanism
// ============================================================

/// Tautological invariant chain: each invariant passes and is available
/// for subsequent obligations.
///
/// NOT DISCRIMINATING for the assume step (flat-scope limitation): the
/// assertions would also pass without the invariant assumptions because
/// u32 >= 0 is a BV tautology the solver knows natively. This test
/// exercises the code path where verified invariants are accumulated
/// and passed to subsequent obligations.
#[test]
fn test_tautological_invariant_chain_cascading() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.declare_var_typed("y", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));

        // Invariant 1: x >= 0 (tautology for u32)
        ctx.push_obligation(ProofObligation::loop_invariant("inv_1", "x >= 0"));

        // Invariant 2: y >= 0 (tautology for u32)
        ctx.push_obligation(ProofObligation::loop_invariant("inv_2", "y >= 0"));

        // Assertion using both invariant facts
        ctx.push_obligation(ProofObligation::assert("both_nonneg", "x >= 0 && y >= 0"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Tautological invariant chain should verify: {:?}",
            result
        );
    })
}

/// Frame condition invariant chain: verified invariant is available for
/// subsequent invariant base case.
///
/// NOT DISCRIMINATING for the assume step (flat-scope limitation):
/// invariant 2's base case `n > 0` is provable from the precondition
/// `n > 0` directly, without needing invariant 1 to be assumed.
/// This exercises the cascading code path through frame condition mode.
#[test]
fn test_frame_condition_invariant_chain_cascading() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        ctx.push_obligation(ProofObligation::assume("n_pos", "n > 0"));
        ctx.push_obligation(ProofObligation::assume("i_init", "i == 0"));

        // Invariant 1: n > 0 (frame condition: n unmodified)
        ctx.push_obligation(ProofObligation::loop_invariant("inv_n_pos", "n > 0"));
        ctx.set_loop_modified_vars("inv_n_pos", vec!["i".to_string()]);

        // Invariant 2: n > 0 (same — exercises cascading path)
        ctx.push_obligation(ProofObligation::loop_invariant("inv_n_pos_2", "n > 0"));
        ctx.set_loop_modified_vars("inv_n_pos_2", vec!["i".to_string()]);

        // Assertion
        ctx.push_obligation(ProofObligation::assert("post_n_pos", "n > 0"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Frame condition invariant chain should verify: {:?}",
            result
        );
    })
}

// ============================================================
// REDUNDANCY: Explicit demonstration of flat-scope limitation
// ============================================================

/// ARCHITECTURAL LIMITATION: Assertion passes with OR without invariant.
///
/// This test demonstrates the flat-scope redundancy. The assertion `n > 0`
/// is provable from the precondition `n > 0` alone. The invariant `n > 0`
/// adds no new information because preconditions are globally visible.
///
/// When loop body scoping is implemented (#1609), the assertion inside
/// the loop body would only have access to the invariant assumption, not
/// the precondition directly. At that point, removing the assume step
/// would cause the assertion to fail.
#[test]
fn test_assume_step_redundant_in_flat_scope() {
    // Test 1: WITH invariant
    let result_with_inv = common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.push_obligation(ProofObligation::assume("precond", "n > 0"));
        ctx.push_obligation(ProofObligation::loop_invariant("inv_n", "n > 0"));
        ctx.set_loop_modified_vars("inv_n", vec![]); // n unmodified → frame condition
        ctx.push_obligation(ProofObligation::assert("post", "n > 0"));
        ctx.verify()
    });

    // Test 2: WITHOUT invariant (same assertion, same precondition)
    let result_without_inv = common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.push_obligation(ProofObligation::assume("precond", "n > 0"));
        // NO invariant — assertion relies on precondition alone
        ctx.push_obligation(ProofObligation::assert("post", "n > 0"));
        ctx.verify()
    });

    // Both pass — demonstrating the invariant assumption is redundant
    assert!(
        matches!(result_with_inv, VerifyResult::Verified),
        "With invariant should verify: {:?}",
        result_with_inv
    );
    assert!(
        matches!(result_without_inv, VerifyResult::Verified),
        "Without invariant should also verify (flat-scope redundancy): {:?}",
        result_without_inv
    );
}

/// ARCHITECTURAL LIMITATION: Derived fact is redundant too.
///
/// Even when the invariant expresses a DERIVED fact (a + b == 15 from
/// a == 5 and b == 10), the same preconditions that prove the base case
/// also prove the assertion directly. The solver derives the same fact
/// either way because preconditions are globally visible.
#[test]
fn test_derived_invariant_fact_redundant_in_flat_scope() {
    // WITH invariant
    let result_with = common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.declare_var_typed("b", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
        ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));

        // Derived fact: a + b == 15
        ctx.push_obligation(ProofObligation::loop_invariant("inv_sum", "a + b == 15"));
        ctx.set_loop_modified_vars("inv_sum", vec!["i".to_string()]);

        ctx.push_obligation(ProofObligation::assert("post_sum", "a + b == 15"));
        ctx.verify()
    });

    // WITHOUT invariant
    let result_without = common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.declare_var_typed("b", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
        ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
        // No invariant — assertion from preconditions directly
        ctx.push_obligation(ProofObligation::assert("post_sum", "a + b == 15"));
        ctx.verify()
    });

    assert!(
        matches!(result_with, VerifyResult::Verified),
        "With derived invariant: {:?}",
        result_with
    );
    assert!(
        matches!(result_without, VerifyResult::Verified),
        "Without derived invariant (flat-scope redundancy): {:?}",
        result_without
    );
}

// ============================================================
// FRAME CONDITION: Assume step with frame-condition-verified invariants
// ============================================================

/// Frame condition invariant assumed → assertion passes.
///
/// NOT DISCRIMINATING (flat-scope): the assertion also passes from
/// preconditions. Exercises the frame condition → assume → assert path.
#[test]
fn test_frame_condition_invariant_assumed_for_assertion() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed(
            "counter",
            trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"),
        );
        ctx.declare_var_typed(
            "limit",
            trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"),
        );

        ctx.push_obligation(ProofObligation::assume("limit_init", "limit == 100"));
        ctx.push_obligation(ProofObligation::assume("counter_init", "counter == 0"));

        // Invariant: limit == 100 (passes frame condition: limit unmodified)
        ctx.push_obligation(ProofObligation::loop_invariant("inv_limit", "limit == 100"));
        ctx.set_loop_modified_vars("inv_limit", vec!["counter".to_string()]);
        ctx.add_loop_guard("inv_limit", "counter < limit");

        // Assertion uses the assumed invariant
        ctx.push_obligation(ProofObligation::assert("post_limit", "limit == 100"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Frame condition invariant + assertion should verify: {:?}",
            result
        );
    })
}

/// Mixed invariant results: first passes (frame condition), second fails
/// (havoc-all). The second invariant's failure should not be masked by
/// the first invariant's assumption.
#[test]
fn test_mixed_invariant_results_correct_failure_reported() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("y", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        ctx.push_obligation(ProofObligation::assume("x_init", "x == 42"));
        ctx.push_obligation(ProofObligation::assume("y_init", "y > 0"));

        // Invariant 1: x == 42 (frame condition: x unmodified — passes)
        ctx.push_obligation(ProofObligation::loop_invariant("inv_x_const", "x == 42"));
        ctx.set_loop_modified_vars("inv_x_const", vec!["y".to_string()]);

        // Invariant 2: y > 0 (havoc-all: NOT tautological for i32 — fails)
        ctx.push_obligation(ProofObligation::loop_invariant("inv_y_pos", "y > 0"));
        // No modified_vars → havoc-all mode

        let result = ctx.verify();

        match &result {
            VerifyResult::Counterexample {
                obligation_name, ..
            } => {
                assert!(
                    obligation_name.contains("inv_y_pos"),
                    "Should fail at second invariant 'inv_y_pos', got: {}",
                    obligation_name
                );
                assert!(
                    obligation_name.contains("inductive step"),
                    "Should fail at inductive step, got: {}",
                    obligation_name
                );
            }
            other => panic!(
                "Expected Counterexample at inv_y_pos inductive step, got: {:?}",
                other
            ),
        }
    })
}

/// Multiple frame-condition invariants: all pass and are assumed.
///
/// NOT DISCRIMINATING (flat-scope): assertions provable from preconditions.
/// Exercises the full cascading path through frame condition mode.
#[test]
fn test_multiple_frame_condition_invariants_all_assumed() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.declare_var_typed("b", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.declare_var_typed("c", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));

        ctx.push_obligation(ProofObligation::assume("a_init", "a == 1"));
        ctx.push_obligation(ProofObligation::assume("b_init", "b == 2"));
        ctx.push_obligation(ProofObligation::assume("c_init", "c == 3"));

        // Three invariants on unmodified vars
        ctx.push_obligation(ProofObligation::loop_invariant("inv_a", "a == 1"));
        ctx.set_loop_modified_vars("inv_a", vec!["i".to_string()]);

        ctx.push_obligation(ProofObligation::loop_invariant("inv_b", "b == 2"));
        ctx.set_loop_modified_vars("inv_b", vec!["i".to_string()]);

        ctx.push_obligation(ProofObligation::loop_invariant("inv_c", "c == 3"));
        ctx.set_loop_modified_vars("inv_c", vec!["i".to_string()]);

        // Assertion combining all three
        ctx.push_obligation(ProofObligation::assert(
            "post_all",
            "a == 1 && b == 2 && c == 3",
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Multiple frame condition invariants should all verify: {:?}",
            result
        );
    })
}
