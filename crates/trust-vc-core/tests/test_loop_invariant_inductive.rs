//! Tests for LoopInvariant obligation kind: assert-then-assume semantics.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! LoopInvariant obligations are both:
//!   1. Asserted (base case: must hold from existing assumptions)
//!   2. Assumed (inductive hypothesis: available for subsequent obligations)
//!
//! This fixes #1544 where invariant!() only collected Assert, missing the
//! inductive assumption step.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests invoke ay verification through `VerificationContext::verify()`.

use trust_vc_core::vc::{ObligationKind, ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

mod common;

fn obligation(name: &str, condition: &str, kind: ObligationKind) -> ProofObligation {
    ProofObligation::new(name, condition, kind)
}

/// A trivially true loop invariant should verify.
#[test]
fn test_loop_invariant_true_verifies() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.push_obligation(obligation(
            "loop_invariant",
            "true",
            ObligationKind::LoopInvariant,
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "LoopInvariant(true) must verify, got: {:?}",
            result
        );
    })
}

/// A trivially false loop invariant should produce a counterexample.
#[test]
fn test_loop_invariant_false_fails() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.push_obligation(obligation(
            "loop_invariant",
            "false",
            ObligationKind::LoopInvariant,
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "LoopInvariant(false) must produce Counterexample, got: {:?}",
            result
        );
    })
}

/// Loop invariant provable from precondition but NOT universally valid.
///
/// `x > 0` is provable from `requires(x > 0)` (base case passes), but
/// the inductive step (havoc pattern) rejects it because `x > 0` is not
/// universally valid over all i32 values (counterexample: x = 0 or x = -1).
///
/// This is a known false negative of the havoc overapproximation (#1609).
/// The invariant IS preserved by loops that maintain x > 0, but the encoder
/// cannot verify this without loop body encoding.
#[test]
fn test_loop_invariant_from_precondition_rejected_by_inductive_step() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // Precondition: x > 0
        ctx.push_obligation(obligation("requires", "x > 0", ObligationKind::Requires));

        // Loop invariant: x > 0 (base case provable, inductive step fails)
        ctx.push_obligation(obligation(
            "loop_invariant",
            "x > 0",
            ObligationKind::LoopInvariant,
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant must fail inductive step even with precondition, got: {:?}",
            result
        );
    })
}

/// Loop invariant NOT provable without precondition.
/// LoopInvariant(x > 0) alone should fail for unconstrained x.
#[test]
fn test_loop_invariant_without_precondition_fails() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        ctx.push_obligation(obligation(
            "loop_invariant",
            "x > 0",
            ObligationKind::LoopInvariant,
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "LoopInvariant(x > 0) without preconditions must fail, got: {:?}",
            result
        );
    })
}

/// Invariant base case + post-loop assertion: inductive step blocks non-tautological.
///
/// `x > 0` passes the base case (from precondition) but fails the inductive
/// step because it's not universally valid over all i32 values.
///
/// The inductive step check (#1609) fires BEFORE the invariant is assumed,
/// so the post-loop assertion is never reached.
#[test]
fn test_loop_invariant_with_post_assertion_blocked_by_inductive_step() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // Precondition: x > 0
        ctx.push_obligation(obligation("requires", "x > 0", ObligationKind::Requires));

        // Loop invariant: x > 0 (base case passes, inductive step fails)
        ctx.push_obligation(obligation(
            "loop_invariant",
            "x > 0",
            ObligationKind::LoopInvariant,
        ));

        // Post-loop assertion: x >= 1 (never reached due to inductive step failure)
        ctx.push_obligation(obligation(
            "post_loop_assertion",
            "x >= 1",
            ObligationKind::Assert,
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant must fail inductive step, got: {:?}",
            result
        );
    })
}

/// Invariant + postcondition: inductive step blocks non-tautological invariant.
///
/// `n > 0` passes base case but fails inductive step (not universally valid).
/// The postcondition is never checked because the invariant loop exits early.
#[test]
fn test_loop_invariant_with_postcondition_blocked_by_inductive_step() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // Precondition
        ctx.push_obligation(obligation("requires", "n > 0", ObligationKind::Requires));

        // Loop invariant (base case passes, inductive step fails)
        ctx.push_obligation(obligation(
            "loop_invariant",
            "n > 0",
            ObligationKind::LoopInvariant,
        ));

        // Postcondition (never reached)
        ctx.push_obligation(obligation("ensures", "n > 0", ObligationKind::Ensures));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant must fail inductive step, got: {:?}",
            result
        );
    })
}

/// Multiple invariants: first non-tautological invariant blocks all.
///
/// `x > 0` passes base case but fails inductive step. The second invariant
/// and assertion are never reached.
#[test]
fn test_invariant_ordering_first_nontaut_blocks() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("y", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // Preconditions
        ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
        ctx.push_obligation(ProofObligation::assume("y_positive", "y > 0"));

        // Invariant 1: x > 0 (base case passes, inductive step fails)
        ctx.push_obligation(obligation(
            "invariant_x",
            "x > 0",
            ObligationKind::LoopInvariant,
        ));

        // Invariant 2: y > 0 (never reached)
        ctx.push_obligation(obligation(
            "invariant_y",
            "y > 0",
            ObligationKind::LoopInvariant,
        ));

        // Assertion (never reached)
        ctx.push_obligation(obligation(
            "both_positive",
            "x > 0 && y > 0",
            ObligationKind::Assert,
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant must fail inductive step, got: {:?}",
            result
        );
    })
}

/// Verify that LoopInvariant is counted as an assertion in has_assertions().
#[test]
fn test_loop_invariant_counts_as_assertion() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();

        // Empty context has no assertions
        assert!(!ctx.has_assertions());

        // Adding a LoopInvariant should count as an assertion
        ctx.push_obligation(obligation(
            "loop_invariant",
            "x > 0",
            ObligationKind::LoopInvariant,
        ));
        assert!(ctx.has_assertions());
    })
}

/// Multiple non-tautological invariants: first one blocks at inductive step.
///
/// `i >= 0` is not universally valid for signed i32 (counterexample: i = -1).
/// The inductive step rejects it before the second invariant is checked.
#[test]
fn test_multiple_loop_invariants_blocked_by_inductive_step() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // Preconditions
        ctx.push_obligation(ProofObligation::assume("i_bound", "i >= 0"));
        ctx.push_obligation(ProofObligation::assume("n_positive", "n > 0"));
        ctx.push_obligation(ProofObligation::assume("i_le_n", "i <= n"));

        // Invariant 1: i >= 0 (base case passes, inductive step fails)
        ctx.push_obligation(obligation(
            "invariant_1",
            "i >= 0",
            ObligationKind::LoopInvariant,
        ));

        // Invariant 2 and assertion never reached
        ctx.push_obligation(obligation(
            "invariant_2",
            "i <= n",
            ObligationKind::LoopInvariant,
        ));

        ctx.push_obligation(obligation(
            "bounded",
            "i >= 0 && i <= n",
            ObligationKind::Assert,
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant must fail inductive step, got: {:?}",
            result
        );
    })
}

/// INDUCTIVE STEP TEST: Non-tautological invariant rejected by havoc check (#1609).
///
/// The invariant `x < 5` is true at entry (x = 0) but not universally valid
/// (x could be 6). The inductive step (havoc pattern) catches this: in a fresh
/// encoder with unconstrained x, `x < 5` is falsifiable.
///
/// Before #1609 fix: base case passes, invariant assumed, Verified (UNSOUND).
/// After #1609 fix: base case passes, inductive step fails, Counterexample (SOUND).
#[test]
fn test_non_tautological_invariant_rejected_by_inductive_step() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // Precondition: x == 0 (establishes base case)
        ctx.push_obligation(ProofObligation::assume("x_init", "x == 0"));

        // Loop invariant: x < 5 (true at entry, but NOT universally valid)
        ctx.push_obligation(obligation(
            "loop_invariant_x_lt_5",
            "x < 5",
            ObligationKind::LoopInvariant,
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant must fail inductive step, got: {:?}",
            result
        );
    })
}

/// INDUCTIVE STEP TEST: Tautological invariant passes both base and inductive (#1609).
///
/// `true` is universally valid, so the inductive step passes trivially.
#[test]
fn test_tautological_invariant_passes_inductive_step() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();

        ctx.push_obligation(obligation(
            "loop_invariant_true",
            "true",
            ObligationKind::LoopInvariant,
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Tautological invariant must pass inductive step, got: {:?}",
            result
        );
    })
}

/// INDUCTIVE STEP TEST: Unsigned non-negativity invariant passes (#1609).
///
/// For unsigned types (u32), `x >= 0` is a tautology because unsigned BV
/// values are always non-negative. The inductive step should pass because
/// the sort constraint makes the invariant universally valid.
#[test]
fn test_unsigned_nonneg_invariant_passes_inductive_step() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));

        // For u32, x >= 0 is always true (unsigned BV semantics)
        ctx.push_obligation(obligation(
            "loop_invariant_nonneg",
            "x >= 0",
            ObligationKind::LoopInvariant,
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Unsigned non-negativity invariant must pass, got: {:?}",
            result
        );
    })
}

/// DISCRIMINATING TEST: Loop invariant assume step is required for assertion.
///
/// This test constructs a scenario where:
/// - There are NO assumptions that can prove the final assertion
/// - The first LoopInvariant (x > 0) IS provable from the precondition (x >= 1)
/// - The second LoopInvariant (y > 0) depends on the ASSUMED first invariant plus
///   an unrelated fact
/// - The final assertion (x > 0) is ONLY provable via the invariant assume step
///
/// If the invariant assume step were broken, the assertion would fail because
/// the precondition (x >= 1) alone doesn't establish (x > 0) in BV semantics
/// after the invariant check. Actually: x >= 1 DOES prove x > 0. We need a
/// scenario where the precondition establishes the invariant but the assertion
/// requires a DIFFERENT fact that only the assumed invariant provides.
///
/// Strategy: Use two variables where:
/// - Precondition: a == 5 (establishes invariant_1: a == 5)
/// - Invariant_1: a == 5 (base case provable)
/// - Invariant_2: a + b == 10 (base case provable from a == 5 && b == 5)
/// - Assertion: a + b == 10 (NOT provable without invariant_2 being assumed,
///   because b is unconstrained in the assertion scope without the invariant)
///
/// Wait — b == 5 is also an assumption. Let me use a different approach:
/// Only precondition is a == 5. Invariant_1 is a == 5 (provable).
/// Then assertion is a == 5 — but that's provable from precondition.
///
/// The real issue is: in the current flat architecture, ALL assumptions are
/// visible everywhere. There's no scope isolation. So the invariant assume
/// step is always redundant as long as preconditions exist.
///
/// This test DOCUMENTS that the assume step cannot be discriminated in the
/// current architecture and marks the expected failure condition.
#[test]
fn test_invariant_assume_step_discrimination_limited_by_flat_scope() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("y", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // NO preconditions at all — the assertion should ONLY be provable
        // if the invariant is assumed after being verified.

        // Invariant: x > 0 (base case NOT provable — x is unconstrained!)
        ctx.push_obligation(obligation(
            "loop_invariant_x",
            "x > 0",
            ObligationKind::LoopInvariant,
        ));

        // This invariant's base case should FAIL because x is unconstrained.
        // The encoder should return Counterexample at the invariant base case check.
        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Invariant base case with unconstrained x must fail, got: {:?}",
            result
        );
    })
}

/// Chain dependency: non-tautological invariant blocked by inductive step.
///
/// `a >= 0` is not universally valid for signed i32 (counterexample: a = -1).
/// The inductive step rejects it even though the precondition `a == 5`
/// establishes the base case.
#[test]
fn test_invariant_chain_dependency_blocked_by_inductive_step() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // Precondition: a == 5
        ctx.push_obligation(ProofObligation::assume("precond", "a == 5"));

        // Invariant 1: a >= 0 (base case passes from precondition, inductive step fails)
        ctx.push_obligation(obligation(
            "invariant_1",
            "a >= 0",
            ObligationKind::LoopInvariant,
        ));

        // Invariant 2 and assertion never reached
        ctx.push_obligation(obligation(
            "invariant_2",
            "a >= 0",
            ObligationKind::LoopInvariant,
        ));

        ctx.push_obligation(ProofObligation::assert("post_loop", "a >= 0"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Non-tautological invariant must fail inductive step, got: {:?}",
            result
        );
    })
}

// --- Frame condition tests (#1609 Mode 2) ---
//
// These tests use loop_modified_vars and loop_guards to enable the frame
// condition inductive step, which is less conservative than the havoc-all
// tautology check. Invariants that depend on unmodified variables can now
// pass because those variables retain their type constraints via the
// pre-state frame condition.

/// FRAME CONDITION: Invariant `i <= n` passes when only `i` is modified.
///
/// Without frame condition (havoc-all): `i <= n` fails because both `i` and `n`
/// are havoced, so there exist values where `i > n`.
///
/// With frame condition: `n` retains its pre-state value (frame: `n == n_pre`).
/// The invariant `i_pre <= n_pre` is assumed (inductive hypothesis). The guard
/// `i_pre < n_pre` is assumed. Since `n == n_pre`, the post-state `n` is
/// constrained. But `i` is havoced (modified by loop body), so we check:
/// does there exist `i` such that `i > n`? Yes (i could be anything).
///
/// Wait — this still fails because `i` is unconstrained in the post-state.
/// The frame condition only preserves `n`'s value, not `i`'s relationship to `n`.
/// This is CORRECT: without body encoding, we can't prove `i <= n` is preserved
/// because the body could set `i` to any value.
///
/// The frame condition IS useful for invariants on UNMODIFIED variables:
/// e.g., `n > 0` when only `i` is modified — `n` retains its pre-state value.
#[test]
fn test_frame_condition_unmodified_var_invariant_passes() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // Precondition: n > 0
        ctx.push_obligation(ProofObligation::assume("n_positive", "n > 0"));

        // Loop invariant: n > 0 (only depends on unmodified variable)
        ctx.push_obligation(obligation(
            "invariant_n_positive",
            "n > 0",
            ObligationKind::LoopInvariant,
        ));

        // Specify that only `i` is modified by the loop body
        ctx.set_loop_modified_vars("invariant_n_positive", vec!["i".to_string()]);
        // Guard: i < n
        ctx.add_loop_guard("invariant_n_positive", "i < n");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Invariant on unmodified variable must pass with frame condition, got: {:?}",
            result
        );
    })
}

/// FRAME CONDITION: Same invariant (`n > 0`) fails without modified_vars (havoc-all).
///
/// Without frame condition, `n > 0` is not universally valid for signed i32
/// (counterexample: n = 0 or n = -1). This test confirms the havoc-all path
/// rejects it, demonstrating the frame condition improvement.
#[test]
fn test_havoc_all_rejects_unmodified_var_invariant() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // Precondition: n > 0
        ctx.push_obligation(ProofObligation::assume("n_positive", "n > 0"));

        // Loop invariant: n > 0 (NOT universally valid for i32)
        ctx.push_obligation(obligation(
            "invariant_n_positive",
            "n > 0",
            ObligationKind::LoopInvariant,
        ));

        // NO loop_modified_vars set — uses havoc-all
        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Havoc-all must reject non-tautological invariant, got: {:?}",
            result
        );
    })
}

/// FRAME CONDITION: Modified variable invariant still fails (sound).
///
/// `i >= 0` with only `i` modified: the post-state `i` is havoced
/// (unconstrained), so there exist i32 values where `i < 0`. The frame
/// condition correctly rejects this because the invariant depends on a
/// modified variable.
#[test]
fn test_frame_condition_modified_var_invariant_still_fails() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

        // Precondition: i >= 0
        ctx.push_obligation(ProofObligation::assume("i_nonneg", "i >= 0"));

        // Loop invariant: i >= 0 (depends on modified variable)
        ctx.push_obligation(obligation(
            "invariant_i_nonneg",
            "i >= 0",
            ObligationKind::LoopInvariant,
        ));

        // i is modified by the loop body
        ctx.set_loop_modified_vars("invariant_i_nonneg", vec!["i".to_string()]);

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Invariant on modified variable must still fail (sound), got: {:?}",
            result
        );
    })
}

/// FRAME CONDITION: Unsigned invariant on unmodified var passes (BV semantics).
///
/// `n >= 0` for u32 is always true (BV unsigned semantics). With frame
/// condition and `n` unmodified, it passes. This also passes without frame
/// condition (it's a tautology for unsigned types), but demonstrates the
/// frame condition path works with unsigned BV types.
#[test]
fn test_frame_condition_unsigned_unmodified_passes() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));

        // Loop invariant: n >= 0 (tautology for u32, also passes with frame)
        ctx.push_obligation(obligation(
            "invariant_n_nonneg",
            "n >= 0",
            ObligationKind::LoopInvariant,
        ));

        ctx.set_loop_modified_vars("invariant_n_nonneg", vec!["i".to_string()]);

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Unsigned invariant on unmodified var must pass, got: {:?}",
            result
        );
    })
}
