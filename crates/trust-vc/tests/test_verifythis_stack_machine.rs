// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 67 — Stack Machine / RPN Evaluator VCs (Groups A–D).
//!
//! A stack machine evaluates Reverse Polish Notation (RPN) expressions:
//!   - `push(v)`: push value v onto stack, depth increases by 1.
//!   - `add`: pop two values, push their sum, depth decreases by 1.
//!   - `mul`: pop two values, push their product, depth decreases by 1.
//!
//! Stack is modeled as a Seq<i64>. `sp` (stack pointer) tracks depth.
//! Invariant: sp >= 0 at all times (underflow protection).
//!
//! Groups A–D: Init, Push/Pop Step, Invariant, Full evaluation.
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

fn assume_seq_i64(ctx: &mut VerificationContext, name: &str, values: &[i64]) {
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(
        &format!("{name}_len"),
        &format!("{name}.len() == {}", values.len()),
    );
    for (index, value) in values.iter().enumerate() {
        ctx.push_assume(
            &format!("{name}_{index}"),
            &format!("{name}.index({index}) == {value}"),
        );
    }
}

// ========================================================================
// GROUP A: Init — empty stack
// ========================================================================

/// Tier 67a: Init — empty stack with capacity 10.
#[test]
fn test_vt_tier67a_empty_stack_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("sp", "u64");
    ctx.declare_var_parsed("cap", "u64");

    ctx.push_assume("sp_init", "sp == 0");
    ctx.push_assume("cap_val", "cap == 10");

    ctx.push_assert("sp_in_range", "sp <= cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 67a: empty stack init should verify, got: {:?}",
        result,
    );
}

/// Tier 67a: Init — symbolic capacity, sp=0.
#[test]
fn test_vt_tier67a_symbolic_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("sp", "u64");
    ctx.declare_var_parsed("cap", "u64");

    ctx.push_assume("sp_init", "sp == 0");
    ctx.push_assume("cap_bound", "cap >= 1 && cap <= 100");

    ctx.push_assert("sp_le_cap", "sp <= cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 67a: symbolic init should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Step — push, add, multiply operations
// ========================================================================

/// Tier 67b: Push — push value 42 onto empty stack.
/// stack = [_, _, ...], sp=0 → write 42 at index 0, sp_next=1.
#[test]
fn test_vt_tier67b_push_to_empty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("sp", "u64");
    ctx.declare_var_parsed("sp_next", "u64");
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("val", "i64");

    ctx.push_assume("sp_val", "sp == 0");
    ctx.push_assume("sp_next_val", "sp_next == 1");
    ctx.push_assume("cap_val", "cap == 10");
    ctx.push_assume("val_val", "val == 42");

    // Pre: not full
    ctx.push_assert("not_full", "sp < cap");
    // Post: sp increases by 1
    ctx.push_assert("sp_inc", "sp_next == sp + 1");
    // Post: invariant preserved
    ctx.push_assert("sp_next_in_range", "sp_next <= cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 67b: push to empty should verify, got: {:?}",
        result,
    );
}

/// Tier 67b: Push — push onto non-empty stack.
/// sp=3, push 7 → sp_next=4, stack[3]=7.
#[test]
fn test_vt_tier67b_push_non_empty() {
    let mut ctx = VerificationContext::new();
    // Stack before push: [10, 20, 30, ?, ?, ...]
    assume_seq_i64(&mut ctx, "stack", &[10, 20, 30, 0, 0, 0, 0, 0, 0, 0]);
    // Stack after push: [10, 20, 30, 7, ?, ...]
    assume_seq_i64(&mut ctx, "stack_next", &[10, 20, 30, 7, 0, 0, 0, 0, 0, 0]);

    ctx.declare_var_parsed("sp", "u64");
    ctx.declare_var_parsed("sp_next", "u64");
    ctx.push_assume("sp_val", "sp == 3");
    ctx.push_assume("sp_next_val", "sp_next == 4");

    // Push wrote at index sp=3
    ctx.push_assert("written", "stack_next.index(3) == 7");
    // Frame: indices below sp unchanged
    ctx.push_assert("frame_0", "stack_next.index(0) == stack.index(0)");
    ctx.push_assert("frame_1", "stack_next.index(1) == stack.index(1)");
    ctx.push_assert("frame_2", "stack_next.index(2) == stack.index(2)");
    ctx.push_assert("sp_inc", "sp_next == sp + 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 67b: push non-empty should verify, got: {:?}",
        result,
    );
}

/// Tier 67b: Add — pop 30 and 20, push 50. sp=3→2.
/// stack = [10, 20, 30, ...], sp=3 → stack_next = [10, 50, ...], sp_next=2.
#[test]
fn test_vt_tier67b_add_operation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("sp", "u64");
    ctx.declare_var_parsed("sp_next", "u64");
    ctx.declare_var_parsed("a", "i64");
    ctx.declare_var_parsed("b", "i64");
    ctx.declare_var_parsed("result", "i64");

    ctx.push_assume("sp_val", "sp == 3");
    ctx.push_assume("sp_next_val", "sp_next == 2");
    // Pop top two: stack[sp-1]=30, stack[sp-2]=20
    ctx.push_assume("a_val", "a == 30"); // top
    ctx.push_assume("b_val", "b == 20"); // second
    ctx.push_assume("result_val", "result == 50");

    // Pre: at least 2 elements
    ctx.push_assert("enough_operands", "sp >= 2");
    // Post: result is sum
    ctx.push_assert("sum_correct", "result == a + b");
    // Post: sp decreases by 1 (pop 2, push 1)
    ctx.push_assert("sp_dec", "sp_next == sp - 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 67b: add operation should verify, got: {:?}",
        result,
    );
}

/// Tier 67b: Mul — pop 5 and 7, push 35. sp=2→1.
#[test]
fn test_vt_tier67b_mul_operation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("sp", "u64");
    ctx.declare_var_parsed("sp_next", "u64");
    ctx.declare_var_parsed("a", "i64");
    ctx.declare_var_parsed("b", "i64");
    ctx.declare_var_parsed("result", "i64");

    ctx.push_assume("sp_val", "sp == 2");
    ctx.push_assume("sp_next_val", "sp_next == 1");
    ctx.push_assume("a_val", "a == 5");
    ctx.push_assume("b_val", "b == 7");
    ctx.push_assume("result_val", "result == 35");

    ctx.push_assert("enough_operands", "sp >= 2");
    ctx.push_assert("product_correct", "result == a * b");
    ctx.push_assert("sp_dec", "sp_next == sp - 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 67b: mul operation should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Invariant — sp tracking, underflow protection
// ========================================================================

/// Tier 67c: Invariant — push always increases sp by 1 (bounded by cap).
#[test]
fn test_vt_tier67c_push_sp_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("sp", "u64");
    ctx.declare_var_parsed("sp_next", "u64");
    ctx.declare_var_parsed("cap", "u64");

    ctx.push_assume("cap_bound", "cap >= 1 && cap <= 100");
    ctx.push_assume("sp_bound", "sp < cap"); // pre: not full
    ctx.push_assume("sp_next_def", "sp_next == sp + 1");

    ctx.push_assert("sp_next_le_cap", "sp_next <= cap");
    ctx.push_assert("sp_next_pos", "sp_next >= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 67c: push sp invariant should verify, got: {:?}",
        result,
    );
}

/// Tier 67c: Invariant — binary op (add/mul) requires sp >= 2.
/// After op, sp >= 1 (one result on stack).
#[test]
fn test_vt_tier67c_binop_sp_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("sp", "u64");
    ctx.declare_var_parsed("sp_next", "u64");

    ctx.push_assume("sp_ge2", "sp >= 2");
    ctx.push_assume("sp_bound", "sp <= 100");
    ctx.push_assume("sp_next_def", "sp_next == sp - 1");

    ctx.push_assert("sp_next_ge1", "sp_next >= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 67c: binop sp invariant should verify, got: {:?}",
        result,
    );
}

/// Tier 67c: Invariant — well-formed RPN expression ends with sp=1.
/// Expression: "3 5 + 2 *" → push 3, push 5, add, push 2, mul.
/// sp trace: 0→1→2→1→2→1. Final sp=1.
#[test]
fn test_vt_tier67c_well_formed_rpn_sp_trace() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("sp0", "u64");
    ctx.declare_var_parsed("sp1", "u64");
    ctx.declare_var_parsed("sp2", "u64");
    ctx.declare_var_parsed("sp3", "u64");
    ctx.declare_var_parsed("sp4", "u64");
    ctx.declare_var_parsed("sp5", "u64");

    ctx.push_assume("sp0_val", "sp0 == 0"); // start
    ctx.push_assume("sp1_val", "sp1 == 1"); // push 3
    ctx.push_assume("sp2_val", "sp2 == 2"); // push 5
    ctx.push_assume("sp3_val", "sp3 == 1"); // add
    ctx.push_assume("sp4_val", "sp4 == 2"); // push 2
    ctx.push_assume("sp5_val", "sp5 == 1"); // mul

    // Push: +1
    ctx.push_assert("push_3", "sp1 == sp0 + 1");
    ctx.push_assert("push_5", "sp2 == sp1 + 1");
    // Add: -1
    ctx.push_assert("add_op", "sp3 == sp2 - 1");
    // Push: +1
    ctx.push_assert("push_2", "sp4 == sp3 + 1");
    // Mul: -1
    ctx.push_assert("mul_op", "sp5 == sp4 - 1");
    // Never underflow (all sp >= 0, which is trivial for u64)
    ctx.push_assert("no_underflow_3", "sp3 >= 1");
    ctx.push_assert("no_underflow_5", "sp5 >= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 67c: well-formed RPN sp trace should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Full evaluation + negative tests
// ========================================================================

/// Tier 67d: Full evaluation — "3 5 + 2 *" = (3+5)*2 = 16.
/// Concrete stack trace with Seq.
#[test]
fn test_vt_tier67d_full_eval_3_5_add_2_mul() {
    let mut ctx = VerificationContext::new();

    // Step 0: empty → push 3 → stack = [3]
    assume_seq_i64(&mut ctx, "s1", &[3]);
    // Step 1: push 5 → stack = [3, 5]
    assume_seq_i64(&mut ctx, "s2", &[3, 5]);
    // Step 2: add → pop 5,3, push 8 → stack = [8]
    assume_seq_i64(&mut ctx, "s3", &[8]);
    // Step 3: push 2 → stack = [8, 2]
    assume_seq_i64(&mut ctx, "s4", &[8, 2]);
    // Step 4: mul → pop 2,8, push 16 → stack = [16]
    assume_seq_i64(&mut ctx, "s5", &[16]);

    // Verify each operation
    ctx.push_assert("push_3", "s1.index(0) == 3");
    ctx.push_assert("push_5", "s2.index(1) == 5");
    ctx.push_assert("add_result", "s3.index(0) == s2.index(0) + s2.index(1)");
    ctx.push_assert("push_2", "s4.index(1) == 2");
    ctx.push_assert("mul_result", "s5.index(0) == s4.index(0) * s4.index(1)");
    // Final result
    ctx.push_assert("final_value", "s5.index(0) == 16");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 67d: full eval 3 5 + 2 * = 16 should verify, got: {:?}",
        result,
    );
}

/// Tier 67d: Full evaluation — "2 3 4 * +" = 2 + (3*4) = 14.
/// Evaluates right-to-left associativity of RPN.
#[test]
fn test_vt_tier67d_full_eval_2_3_4_mul_add() {
    let mut ctx = VerificationContext::new();

    ctx.declare_var_parsed("v0", "i64"); // push 2
    ctx.declare_var_parsed("v1", "i64"); // push 3
    ctx.declare_var_parsed("v2", "i64"); // push 4
    ctx.declare_var_parsed("v3", "i64"); // mul: 3*4 = 12
    ctx.declare_var_parsed("v4", "i64"); // add: 2+12 = 14

    ctx.push_assume("v0_val", "v0 == 2");
    ctx.push_assume("v1_val", "v1 == 3");
    ctx.push_assume("v2_val", "v2 == 4");
    ctx.push_assume("v3_val", "v3 == 12"); // 3*4
    ctx.push_assume("v4_val", "v4 == 14"); // 2+12

    ctx.push_assert("mul_correct", "v3 == v1 * v2");
    ctx.push_assert("add_correct", "v4 == v0 + v3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 67d: full eval 2 3 4 * + = 14 should verify, got: {:?}",
        result,
    );
}

/// Tier 67d: Full evaluation — "7 2 - 3 *" = (7-2)*3 = 15.
/// Tests subtraction via add-with-negation.
#[test]
fn test_vt_tier67d_full_eval_subtraction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "i64");
    ctx.declare_var_parsed("b", "i64");
    ctx.declare_var_parsed("diff", "i64");
    ctx.declare_var_parsed("c", "i64");
    ctx.declare_var_parsed("result", "i64");

    ctx.push_assume("a_val", "a == 7");
    ctx.push_assume("b_val", "b == 2");
    ctx.push_assume("diff_val", "diff == 5"); // 7 - 2
    ctx.push_assume("c_val", "c == 3");
    ctx.push_assume("result_val", "result == 15"); // 5 * 3

    ctx.push_assert("sub_correct", "diff == a - b");
    ctx.push_assert("mul_correct", "result == diff * c");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 67d: subtraction eval (7-2)*3 = 15 should verify, got: {:?}",
        result,
    );
}

/// Tier 67d: Negative — underflow on add with only 1 element.
/// If sp=1 and we try to add, sp_next would be 0, but we need sp >= 2.
#[test]
fn test_vt_tier67d_underflow_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("sp", "u64");

    ctx.push_assume("sp_val", "sp == 1");

    // Trying to do a binary op with sp=1 violates the precondition
    ctx.push_assert("has_two_operands", "sp >= 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 67d SOUNDNESS: underflow should be rejected, got: {:?}",
        result,
    );
}

/// Tier 67d: Negative — wrong result for "3 5 + 2 *".
/// Claiming (3+5)*2 = 15 instead of 16.
#[test]
fn test_vt_tier67d_wrong_result_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "i64");
    ctx.declare_var_parsed("b", "i64");
    ctx.declare_var_parsed("sum_val", "i64");
    ctx.declare_var_parsed("c", "i64");
    ctx.declare_var_parsed("result", "i64");

    ctx.push_assume("a_val", "a == 3");
    ctx.push_assume("b_val", "b == 5");
    ctx.push_assume("sum_val_v", "sum_val == 8");
    ctx.push_assume("c_val", "c == 2");
    ctx.push_assume("result_val", "result == 15"); // Wrong!

    ctx.push_assert("sum_ok", "sum_val == a + b");
    // Claim: result = sum * c, but 15 != 8*2=16
    ctx.push_assert("wrong_product", "result == sum_val * c");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 67d SOUNDNESS: wrong result should be rejected, got: {:?}",
        result,
    );
}
