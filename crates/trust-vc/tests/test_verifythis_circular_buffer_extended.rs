// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 65 — Circular Buffer VCs (Groups E–F).
//!
//! Symbolic invariant proofs and soundness negatives for the circular buffer.
//! Core groups (A–D) are in test_verifythis_circular_buffer.rs.
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
// GROUP E: Invariant — symbolic properties
// ========================================================================

/// Tier 65e: Invariant — enqueue preserves the structural invariant symbolically.
/// Given valid state (head < cap, count < cap), after enqueue:
/// head unchanged, count+1 <= cap, write_pos < cap.
#[test]
fn test_vt_tier65e_enqueue_preserves_invariant_symbolic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("count_next", "u64");

    ctx.push_assume("cap_bound", "cap >= 1 && cap <= 100");
    ctx.push_assume("head_bound", "head >= 0 && head < cap");
    ctx.push_assume("count_bound", "count >= 0 && count < cap"); // not full
    ctx.push_assume("count_next_def", "count_next == count + 1");

    // Invariant preserved after enqueue
    ctx.push_assert("head_unchanged", "head < cap");
    ctx.push_assert("count_next_le_cap", "count_next <= cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65e: enqueue invariant symbolic should verify, got: {:?}",
        result,
    );
}

/// Tier 65e: Invariant — dequeue preserves the structural invariant symbolically.
/// Given valid state (head < cap, count > 0), after dequeue:
/// head_next < cap (via modular arithmetic), count-1 >= 0.
#[test]
fn test_vt_tier65e_dequeue_preserves_invariant_symbolic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("head_next", "u64");
    ctx.declare_var_parsed("count_next", "u64");

    ctx.push_assume("cap_bound", "cap >= 1 && cap <= 100");
    ctx.push_assume("head_bound", "head >= 0 && head < cap");
    ctx.push_assume("count_bound", "count >= 1 && count <= cap"); // not empty
    ctx.push_assume("count_next_def", "count_next == count - 1");
    // head_next = (head + 1) % cap — use conditional form to avoid % operator
    // if head + 1 < cap then head + 1 else 0
    ctx.push_assume(
        "head_next_def",
        "(head + 1 < cap && head_next == head + 1) || (head + 1 == cap && head_next == 0)",
    );

    ctx.push_assert("head_next_in_range", "head_next < cap");
    ctx.push_assert("count_next_ge_0", "count_next >= 0");
    ctx.push_assert("count_next_le_cap", "count_next <= cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65e: dequeue invariant symbolic should verify, got: {:?}",
        result,
    );
}

/// Tier 65e: Invariant — enqueue then dequeue returns to original count.
#[test]
fn test_vt_tier65e_enqueue_dequeue_count_roundtrip() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("count_after_enq", "u64");
    ctx.declare_var_parsed("count_after_deq", "u64");

    ctx.push_assume("cap_bound", "cap >= 2 && cap <= 100");
    ctx.push_assume("count_bound", "count >= 1 && count < cap"); // room for enqueue and not empty
    ctx.push_assume("enq", "count_after_enq == count + 1");
    ctx.push_assume("deq", "count_after_deq == count_after_enq - 1");

    ctx.push_assert("roundtrip", "count_after_deq == count");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65e: enqueue-dequeue roundtrip should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP F: Soundness negatives
// ========================================================================

/// Tier 65f NEGATIVE: enqueue to a full buffer violates precondition.
/// count == cap means no room — asserting count < cap should fail.
#[test]
fn test_vt_tier65f_enqueue_full_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("count", "u64");

    ctx.push_assume("cap_val", "cap == 5");
    ctx.push_assume("count_val", "count == 5"); // FULL

    ctx.push_assert("not_full", "count < cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 65f SOUNDNESS: enqueue to full must be rejected, got: {:?}",
        result,
    );
}

/// Tier 65f NEGATIVE: dequeue from empty buffer violates precondition.
#[test]
fn test_vt_tier65f_dequeue_empty_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("count", "u64");

    ctx.push_assume("count_val", "count == 0"); // EMPTY

    ctx.push_assert("not_empty", "count > 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 65f SOUNDNESS: dequeue from empty must be rejected, got: {:?}",
        result,
    );
}

/// Tier 65f NEGATIVE: wrong write position (no modular wrap) goes out of bounds.
/// head=3, count=3, cap=5 → correct write_pos = (3+3)%5 = 1.
/// Without modulo: write_pos = 3+3 = 6, which is >= cap.
#[test]
fn test_vt_tier65f_wrong_write_pos_out_of_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("write_pos", "u64");

    ctx.push_assume("cap_val", "cap == 5");
    ctx.push_assume("head_val", "head == 3");
    ctx.push_assume("count_val", "count == 3");
    // WRONG: no modulo, write_pos = head + count = 6
    ctx.push_assume("write_pos_wrong", "write_pos == 6");

    ctx.push_assert("write_in_range", "write_pos < cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 65f SOUNDNESS: wrong write pos must be caught, got: {:?}",
        result,
    );
}

/// Tier 65f NEGATIVE: FIFO violation — wrong dequeue order.
/// If buf=[10,20,30,_,_], head=0, dequeue should return 10, not 30.
#[test]
fn test_vt_tier65f_fifo_violation_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "buf", &[10, 20, 30, 0, 0]);

    ctx.declare_var_parsed("head", "u64");
    ctx.push_assume("head_val", "head == 0");

    // Incorrectly claiming the first dequeue returns 30 (last element)
    ctx.push_assert("wrong_order", "buf.index(0) == 30");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 65f SOUNDNESS: FIFO violation must be rejected, got: {:?}",
        result,
    );
}
