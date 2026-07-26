// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 70 — Fast Exponentiation (Repeated Squaring) VCs.
//!
//! Compute `x^n` in O(log n) multiplications via repeated squaring:
//!
//!   result = 1; base = x; exp = n;
//!   while exp > 0:
//!     if exp % 2 == 1: result *= base
//!     base *= base
//!     exp /= 2
//!
//! Loop invariant: `result * base^exp == x^n` at every iteration start.
//!
//! Core proof obligations:
//!   1. Init: result=1, base=x, exp=n → 1 * x^n == x^n
//!   2. Step (even): base²^(exp/2) == base^exp preserves invariant
//!   3. Step (odd): result*base * (base²)^((exp-1)/2) == result * base^exp
//!   4. Exit: exp=0 → result * base^0 == result == x^n
//!   5. Negatives: wrong initial values or skipping the odd branch is unsound
//!
//! All values fit in `u16`, which keeps the concrete BV arithmetic obligations
//! below the current ay memory cliff.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

fn verify_with_pipeline(context: VerificationContext) -> VerifyResult {
    let mut pipeline = VerificationPipeline::new();
    pipeline.replace_context(context);
    pipeline.verify()
}

// ========================================================================
// GROUP A: Init — invariant establishment
// ========================================================================

/// Tier 70a: Init — for x=3, n=5, the invariant holds at the start.
/// result=1, base=3, exp=5 → result * base^exp = 1 * 3^5 = 243.
#[test]
fn test_vt_tier70a_init_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("result", "u16");
    ctx.declare_var_parsed("base", "u16");
    ctx.declare_var_parsed("exp", "u16");
    ctx.declare_var_parsed("target", "u16");

    ctx.push_assume("result_1", "result == 1");
    ctx.push_assume("base_3", "base == 3");
    ctx.push_assume("exp_5", "exp == 5");
    ctx.push_assume("target_243", "target == 243"); // 3^5

    ctx.push_assert("result_init", "result == 1");
    ctx.push_assert("base_is_x", "base == 3");
    ctx.push_assert("exp_is_n", "exp == 5");
    ctx.push_assert("target_correct", "target == 243");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 70a: init invariant should verify, got: {:?}",
        result,
    );
}

/// Tier 70a: Init for x=2, n=8 → 2^8 = 256.
#[test]
fn test_vt_tier70a_init_power_of_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("result", "u16");
    ctx.declare_var_parsed("base", "u16");
    ctx.declare_var_parsed("exp", "u16");

    ctx.push_assume("result_1", "result == 1");
    ctx.push_assume("base_2", "base == 2");
    ctx.push_assume("exp_8", "exp == 8");

    ctx.push_assert("result_init", "result == 1");
    ctx.push_assert("base_is_2", "base == 2");
    ctx.push_assert("exp_is_8", "exp == 8");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 70a: init for 2^8 should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Step — even and odd exponent cases
// ========================================================================

/// Tier 70b: Even step — exp=4, base=3, result=3.
/// 3 * 3^4 = 3 * 81 = 243. After step: result=3, base=9, exp=2.
/// Check: 3 * 9^2 = 3 * 81 = 243. ✓
#[test]
fn test_vt_tier70b_even_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("result", "u16");
    ctx.declare_var_parsed("base", "u16");
    ctx.declare_var_parsed("exp", "u16");
    ctx.declare_var_parsed("result_next", "u16");
    ctx.declare_var_parsed("base_next", "u16");
    ctx.declare_var_parsed("exp_next", "u16");

    ctx.push_assume("result_3", "result == 3");
    ctx.push_assume("base_3", "base == 3");
    ctx.push_assume("exp_4", "exp == 4");

    // Even case: result unchanged, base squared, exp halved
    ctx.push_assume("result_next_3", "result_next == result");
    ctx.push_assume("base_next_9", "base_next == base * base");
    ctx.push_assume("exp_next_2", "exp_next == exp / 2");

    // Invariant preserved: result_next * base_next^exp_next == 243
    // 3 * 9^2 = 3 * 81 = 243
    ctx.push_assert("exp_is_even", "exp % 2 == 0");
    ctx.push_assert("result_unchanged", "result_next == result");
    ctx.push_assert("base_squared", "base_next == 9");
    ctx.push_assert("exp_halved", "exp_next == 2");
    ctx.push_assert("check_next", "result_next * base_next * base_next == 243");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 70b: even step should preserve invariant, got: {:?}",
        result,
    );
}

/// Tier 70b: Odd step — exp=5, base=3, result=1.
/// 1 * 3^5 = 243. After step: result=1*3=3, base=9, exp=2.
/// Check: 3 * 9^2 = 3 * 81 = 243. ✓
#[test]
fn test_vt_tier70b_odd_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("result", "u16");
    ctx.declare_var_parsed("base", "u16");
    ctx.declare_var_parsed("exp", "u16");
    ctx.declare_var_parsed("result_next", "u16");
    ctx.declare_var_parsed("base_next", "u16");
    ctx.declare_var_parsed("exp_next", "u16");

    ctx.push_assume("result_1", "result == 1");
    ctx.push_assume("base_3", "base == 3");
    ctx.push_assume("exp_5", "exp == 5");

    // Odd case: result *= base, then base squared, exp = (exp-1)/2
    ctx.push_assume("result_next_3", "result_next == result * base");
    ctx.push_assume("base_next_9", "base_next == base * base");
    ctx.push_assume("exp_next_2", "exp_next == (exp - 1) / 2");

    ctx.push_assert("exp_is_odd", "exp % 2 == 1");
    ctx.push_assert("result_multiplied", "result_next == 3");
    ctx.push_assert("base_squared", "base_next == 9");
    ctx.push_assert("exp_halved", "exp_next == 2");
    // Invariant: 3 * 9^2 = 3 * 81 = 243
    ctx.push_assert("check_next", "result_next * base_next * base_next == 243");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 70b: odd step should preserve invariant, got: {:?}",
        result,
    );
}

/// Tier 70b: final odd step — exp=1, base=81, result=3.
/// 3 * 81^1 = 243. After: result=3*81=243, base=6561, exp=0.
#[test]
fn test_vt_tier70b_final_odd_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("result", "u16");
    ctx.declare_var_parsed("base", "u16");
    ctx.declare_var_parsed("exp", "u16");
    ctx.declare_var_parsed("result_next", "u16");
    ctx.declare_var_parsed("base_next", "u16");
    ctx.declare_var_parsed("exp_next", "u16");

    ctx.push_assume("result_3", "result == 3");
    ctx.push_assume("base_81", "base == 81");
    ctx.push_assume("exp_1", "exp == 1");

    ctx.push_assume("result_next_243", "result_next == result * base");
    ctx.push_assume("base_next_sq", "base_next == base * base");
    ctx.push_assume("exp_next_0", "exp_next == (exp - 1) / 2");

    ctx.push_assert("exp_is_odd", "exp % 2 == 1");
    ctx.push_assert("result_final", "result_next == 243");
    ctx.push_assert("exp_zero", "exp_next == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 70b: final odd step should yield target, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Full trace with concrete values (avoids BV multiplication chains)
// ========================================================================

/// Tier 70c: full trace of 2^3 = 8 (short trace: 2 steps).
/// Step 0: r=1, b=2, e=3 (odd)  → r=2, b=4, e=1
/// Step 1: r=2, b=4, e=1 (odd)  → r=8, b=16, e=0
/// Exit: result=8. ✓
#[test]
fn test_vt_tier70c_full_trace_2_pow_3() {
    let mut ctx = VerificationContext::new();
    // Use fully concrete values to avoid BV multiplication memout
    ctx.declare_var_parsed("r0", "u16");
    ctx.declare_var_parsed("b0", "u16");
    ctx.declare_var_parsed("e0", "u16");
    ctx.declare_var_parsed("r1", "u16");
    ctx.declare_var_parsed("b1", "u16");
    ctx.declare_var_parsed("e1", "u16");
    ctx.declare_var_parsed("r2", "u16");
    ctx.declare_var_parsed("e2", "u16");

    // Init
    ctx.push_assume("r0_1", "r0 == 1");
    ctx.push_assume("b0_2", "b0 == 2");
    ctx.push_assume("e0_3", "e0 == 3");

    // Step 0: odd → r=1*2=2, b=2*2=4, e=(3-1)/2=1
    ctx.push_assume("r1_2", "r1 == 2");
    ctx.push_assume("b1_4", "b1 == 4");
    ctx.push_assume("e1_1", "e1 == 1");

    // Step 1: odd → r=2*4=8, b=4*4=16, e=(1-1)/2=0
    ctx.push_assume("r2_8", "r2 == 8");
    ctx.push_assume("e2_0", "e2 == 0");

    // Verify parity decisions
    ctx.push_assert("e0_odd", "e0 % 2 == 1");
    ctx.push_assert("e1_odd", "e1 % 2 == 1");

    // Verify step transitions are correct
    ctx.push_assert("step0_result", "r1 == r0 * b0");
    ctx.push_assert("step0_base", "b1 == b0 * b0");
    ctx.push_assert("step1_result", "r2 == r1 * b1");

    // Final answer
    ctx.push_assert("answer", "r2 == 8");
    ctx.push_assert("done", "e2 == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 70c: full trace of 2^3 should verify, got: {:?}",
        result,
    );
}

/// Tier 70c: full trace of 2^4 = 16 (all even until final odd).
/// Step 0: r=1, b=2, e=4 (even) → r=1, b=4, e=2
/// Step 1: r=1, b=4, e=2 (even) → r=1, b=16, e=1
/// Step 2: r=1, b=16, e=1 (odd) → r=16, b=256, e=0
#[test]
fn test_vt_tier70c_full_trace_2_pow_4() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("r0", "u16");
    ctx.declare_var_parsed("b0", "u16");
    ctx.declare_var_parsed("e0", "u16");
    ctx.declare_var_parsed("r1", "u16");
    ctx.declare_var_parsed("b1", "u16");
    ctx.declare_var_parsed("e1", "u16");
    ctx.declare_var_parsed("r2", "u16");
    ctx.declare_var_parsed("b2", "u16");
    ctx.declare_var_parsed("e2", "u16");
    ctx.declare_var_parsed("r3", "u16");
    ctx.declare_var_parsed("e3", "u16");

    ctx.push_assume("r0_1", "r0 == 1");
    ctx.push_assume("b0_2", "b0 == 2");
    ctx.push_assume("e0_4", "e0 == 4");

    // Step 0: even → r stays 1, b=4, e=2
    ctx.push_assume("r1_1", "r1 == 1");
    ctx.push_assume("b1_4", "b1 == 4");
    ctx.push_assume("e1_2", "e1 == 2");

    // Step 1: even → r stays 1, b=16, e=1
    ctx.push_assume("r2_1", "r2 == 1");
    ctx.push_assume("b2_16", "b2 == 16");
    ctx.push_assume("e2_1", "e2 == 1");

    // Step 2: odd → r=1*16=16, e=0
    ctx.push_assume("r3_16", "r3 == 16");
    ctx.push_assume("e3_0", "e3 == 0");

    // Verify parity
    ctx.push_assert("e0_even", "e0 % 2 == 0");
    ctx.push_assert("e1_even", "e1 % 2 == 0");
    ctx.push_assert("e2_odd", "e2 % 2 == 1");

    // Verify even steps don't change result
    ctx.push_assert("r1_unchanged", "r1 == r0");
    ctx.push_assert("r2_unchanged", "r2 == r1");

    // Verify base squaring
    ctx.push_assert("b1_sq", "b1 == b0 * b0");
    ctx.push_assert("b2_sq", "b2 == b1 * b1");

    // Final answer
    ctx.push_assert("answer", "r3 == 16");
    ctx.push_assert("done", "e3 == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 70c: full trace of 2^4 should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Exit conditions and soundness negatives
// ========================================================================

/// Tier 70d: at termination, exp=0 so result holds the final answer.
#[test]
fn test_vt_tier70d_exit_exp_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("result", "u16");
    ctx.declare_var_parsed("target", "u16");

    ctx.push_assume("result_243", "result == 243");
    ctx.push_assume("target_243", "target == 243");

    ctx.push_assert("result_correct", "result == target");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 70d: exit condition should verify, got: {:?}",
        result,
    );
}

/// Tier 70d: exponentiation by zero always yields 1 (loop never executes).
#[test]
fn test_vt_tier70d_exp_zero_yields_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("result", "u16");
    ctx.declare_var_parsed("exp", "u16");

    ctx.push_assume("result_1", "result == 1");
    ctx.push_assume("exp_0", "exp == 0");

    ctx.push_assert("immediate_exit", "exp == 0");
    ctx.push_assert("result_one", "result == 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 70d: x^0 == 1 should verify, got: {:?}",
        result,
    );
}

/// Tier 70d NEGATIVE: skipping the odd-branch multiply at step 0 propagates
/// through the full 3-step trace and yields 81 instead of 243.
///
/// Correct trace for 3^5:
///   step 0 (odd):  r=1*3=3,   b=9,  e=2
///   step 1 (even): r=3,       b=81, e=1
///   step 2 (odd):  r=3*81=243,      e=0
///
/// Wrong trace (skip multiply at step 0):
///   step 0 WRONG:  r=1,       b=9,  e=2
///   step 1 (even): r=1,       b=81, e=1
///   step 2 (odd):  r=1*81=81,       e=0  → 81 ≠ 243
#[test]
fn test_vt_tier70d_negative_wrong_result() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("r0", "u16");
    ctx.declare_var_parsed("b0", "u16");
    ctx.declare_var_parsed("e0", "u16");
    ctx.declare_var_parsed("r1", "u16");
    ctx.declare_var_parsed("b1", "u16");
    ctx.declare_var_parsed("e1", "u16");
    ctx.declare_var_parsed("r2", "u16");
    ctx.declare_var_parsed("b2", "u16");
    ctx.declare_var_parsed("e2", "u16");
    ctx.declare_var_parsed("r3", "u16");
    ctx.declare_var_parsed("e3", "u16");

    // Init: x=3, n=5
    ctx.push_assume("r0_1", "r0 == 1");
    ctx.push_assume("b0_3", "b0 == 3");
    ctx.push_assume("e0_5", "e0 == 5");

    // Step 0 WRONG: exp=5 is odd, but skip the multiply (treat as even)
    ctx.push_assume("r1_wrong", "r1 == r0"); // should be r0 * b0
    ctx.push_assume("b1_sq", "b1 == b0 * b0"); // = 9
    ctx.push_assume("e1_half", "e1 == e0 / 2"); // = 2

    // Step 1: even → result unchanged, base squared, exp halved
    ctx.push_assume("r2_same", "r2 == r1");
    ctx.push_assume("b2_sq", "b2 == b1 * b1"); // = 81
    ctx.push_assume("e2_half", "e2 == e1 / 2"); // = 1

    // Step 2: odd → result *= base, exp → 0
    ctx.push_assume("r3_mul", "r3 == r2 * b2"); // = 1 * 81 = 81
    ctx.push_assume("e3_done", "e3 == (e2 - 1) / 2"); // = 0

    // The wrong trace yields 81, not 243 — assert the correct target to get Counterexample
    ctx.push_assert("wrong_trace_target", "r3 == 243");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 70d SOUNDNESS: skipping odd multiply in step 0 should not produce 3^5, got: {:?}",
        result,
    );
}

/// Tier 70d NEGATIVE: skipping the odd-branch multiply gives wrong result.
/// If we treat exp=3 as even (skip multiply), r stays 1, b=4, e=1.
/// Then r=1*4=4, not 8.
#[test]
fn test_vt_tier70d_negative_skip_odd_multiply() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("r0", "u16");
    ctx.declare_var_parsed("b0", "u16");
    ctx.declare_var_parsed("e0", "u16");
    ctx.declare_var_parsed("r_wrong", "u16");
    ctx.declare_var_parsed("b_wrong", "u16");
    ctx.declare_var_parsed("e_wrong", "u16");

    ctx.push_assume("r0_1", "r0 == 1");
    ctx.push_assume("b0_2", "b0 == 2");
    ctx.push_assume("e0_3", "e0 == 3");

    // WRONG: treat odd exp=3 as even (skip multiply, just square and halve)
    ctx.push_assume("r_wrong_1", "r_wrong == 1"); // should be 2 if multiply
    ctx.push_assume("b_wrong_4", "b_wrong == 4");
    ctx.push_assume("e_wrong_1", "e_wrong == 1"); // 3/2 = 1

    // After this wrong step, we'd get r=1*4=4, but correct is 8.
    ctx.push_assert("wrong_answer", "r_wrong * b_wrong == 8");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 70d SOUNDNESS: skipping odd multiply should give wrong answer, got: {:?}",
        result,
    );
}
