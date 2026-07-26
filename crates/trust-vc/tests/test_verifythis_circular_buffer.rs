// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 65 — Circular Buffer VCs (Groups A–D).
//!
//! A fixed-capacity circular buffer uses a backing array `buf` of size `cap`
//! with two indices: `head` (read position) and `count` (number of elements).
//! The write position is `(head + count) % cap`.
//!
//! Groups A–D: Init, Enqueue, Dequeue, FIFO ordering.
//! Groups E–F (invariant, negatives): see test_verifythis_circular_buffer_extended.rs.
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
// GROUP A: Init — empty circular buffer
// ========================================================================

/// Tier 65a: Init — empty buffer with capacity 5.
#[test]
fn test_vt_tier65a_empty_buffer_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");

    ctx.push_assume("cap_val", "cap == 5");
    ctx.push_assume("head_val", "head == 0");
    ctx.push_assume("count_val", "count == 0");

    // Invariant holds at initialization
    ctx.push_assert("head_in_range", "head < cap");
    ctx.push_assert("count_in_range", "count <= cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65a: empty buffer init should verify, got: {:?}",
        result,
    );
}

/// Tier 65a: Init — symbolic capacity, head=0, count=0.
#[test]
fn test_vt_tier65a_symbolic_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");

    ctx.push_assume("cap_bound", "cap >= 1 && cap <= 100");
    ctx.push_assume("head_init", "head == 0");
    ctx.push_assume("count_init", "count == 0");

    ctx.push_assert("head_in_range", "head < cap");
    ctx.push_assert("count_in_range", "count <= cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65a: symbolic init should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Enqueue — write element, advance write pointer
// ========================================================================

/// Tier 65b: Enqueue — add one element to empty buffer (cap=5).
/// write_pos = (0 + 0) % 5 = 0; write 42 at index 0; count becomes 1.
#[test]
fn test_vt_tier65b_enqueue_to_empty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("write_pos", "u64");
    ctx.declare_var_parsed("count_next", "u64");

    ctx.push_assume("cap_val", "cap == 5");
    ctx.push_assume("head_val", "head == 0");
    ctx.push_assume("count_val", "count == 0");
    // write_pos = (head + count) % cap = 0
    ctx.push_assume("write_pos_val", "write_pos == 0");
    ctx.push_assume("count_next_val", "count_next == 1");

    // Pre: not full
    ctx.push_assert("not_full", "count < cap");
    // Post: count increases by 1
    ctx.push_assert("count_inc", "count_next == count + 1");
    // Post: invariant preserved
    ctx.push_assert("head_in_range", "head < cap");
    ctx.push_assert("count_next_in_range", "count_next <= cap");
    // Write position is valid
    ctx.push_assert("write_in_range", "write_pos < cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65b: enqueue to empty should verify, got: {:?}",
        result,
    );
}

/// Tier 65b: Enqueue — add element when buffer wraps around.
/// head=3, count=3, cap=5: write_pos = (3+3) % 5 = 1 (wraps!).
#[test]
fn test_vt_tier65b_enqueue_with_wrap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("write_pos", "u64");
    ctx.declare_var_parsed("count_next", "u64");

    ctx.push_assume("cap_val", "cap == 5");
    ctx.push_assume("head_val", "head == 3");
    ctx.push_assume("count_val", "count == 3");
    // (3 + 3) % 5 = 6 % 5 = 1
    ctx.push_assume("write_pos_val", "write_pos == 1");
    ctx.push_assume("count_next_val", "count_next == 4");

    ctx.push_assert("not_full", "count < cap");
    ctx.push_assert("count_inc", "count_next == count + 1");
    ctx.push_assert("write_in_range", "write_pos < cap");
    ctx.push_assert("head_in_range", "head < cap");
    ctx.push_assert("count_next_in_range", "count_next <= cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65b: enqueue with wrap should verify, got: {:?}",
        result,
    );
}

/// Tier 65b: Enqueue — fill buffer to capacity.
/// head=0, count=4, cap=5 → after enqueue count=5 (full).
#[test]
fn test_vt_tier65b_enqueue_to_full() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("write_pos", "u64");
    ctx.declare_var_parsed("count_next", "u64");

    ctx.push_assume("cap_val", "cap == 5");
    ctx.push_assume("head_val", "head == 0");
    ctx.push_assume("count_val", "count == 4");
    ctx.push_assume("write_pos_val", "write_pos == 4"); // (0+4)%5 = 4
    ctx.push_assume("count_next_val", "count_next == 5");

    ctx.push_assert("not_full_pre", "count < cap");
    ctx.push_assert("count_inc", "count_next == count + 1");
    ctx.push_assert("now_full", "count_next == cap");
    ctx.push_assert("write_in_range", "write_pos < cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65b: enqueue to full should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Dequeue — read element, advance head
// ========================================================================

/// Tier 65c: Dequeue — remove from buffer with 3 elements.
/// head=0, count=3, cap=5 → read buf[0], head_next=1, count_next=2.
#[test]
fn test_vt_tier65c_dequeue_basic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("head_next", "u64");
    ctx.declare_var_parsed("count_next", "u64");

    ctx.push_assume("cap_val", "cap == 5");
    ctx.push_assume("head_val", "head == 0");
    ctx.push_assume("count_val", "count == 3");
    // head_next = (head + 1) % cap = 1
    ctx.push_assume("head_next_val", "head_next == 1");
    ctx.push_assume("count_next_val", "count_next == 2");

    // Pre: not empty
    ctx.push_assert("not_empty", "count > 0");
    // Post: count decreases by 1
    ctx.push_assert("count_dec", "count_next == count - 1");
    // Post: head advances (wrapping)
    ctx.push_assert("head_advances", "head_next == head + 1");
    // Post: invariant preserved
    ctx.push_assert("head_next_in_range", "head_next < cap");
    ctx.push_assert("count_next_in_range", "count_next <= cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65c: basic dequeue should verify, got: {:?}",
        result,
    );
}

/// Tier 65c: Dequeue — head wraps around.
/// head=4, count=2, cap=5 → head_next = (4+1) % 5 = 0.
#[test]
fn test_vt_tier65c_dequeue_head_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("head_next", "u64");
    ctx.declare_var_parsed("count_next", "u64");

    ctx.push_assume("cap_val", "cap == 5");
    ctx.push_assume("head_val", "head == 4");
    ctx.push_assume("count_val", "count == 2");
    ctx.push_assume("head_next_val", "head_next == 0"); // (4+1)%5 = 0
    ctx.push_assume("count_next_val", "count_next == 1");

    ctx.push_assert("not_empty", "count > 0");
    ctx.push_assert("count_dec", "count_next == count - 1");
    ctx.push_assert("head_next_in_range", "head_next < cap");
    ctx.push_assert("count_next_in_range", "count_next <= cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65c: dequeue head wrap should verify, got: {:?}",
        result,
    );
}

/// Tier 65c: Dequeue — empty the buffer.
/// head=2, count=1, cap=5 → dequeue last element, count_next=0.
#[test]
fn test_vt_tier65c_dequeue_to_empty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("head_next", "u64");
    ctx.declare_var_parsed("count_next", "u64");

    ctx.push_assume("cap_val", "cap == 5");
    ctx.push_assume("head_val", "head == 2");
    ctx.push_assume("count_val", "count == 1");
    ctx.push_assume("head_next_val", "head_next == 3"); // (2+1)%5 = 3
    ctx.push_assume("count_next_val", "count_next == 0");

    ctx.push_assert("not_empty", "count > 0");
    ctx.push_assert("count_dec", "count_next == count - 1");
    ctx.push_assert("head_next_in_range", "head_next < cap");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65c: dequeue to empty should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: FIFO ordering — elements come out in insertion order
// ========================================================================

/// Tier 65d: FIFO — enqueue 10,20,30 then dequeue gets 10 first.
/// Concrete trace with a backing Seq.
#[test]
fn test_vt_tier65d_fifo_concrete_trace() {
    let mut ctx = VerificationContext::new();
    // After enqueue(10), enqueue(20), enqueue(30):
    // buf = [10, 20, 30, ?, ?], head=0, count=3
    assume_seq_i64(&mut ctx, "buf", &[10, 20, 30, 0, 0]);

    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.push_assume("cap_val", "cap == 5");
    ctx.push_assume("head_val", "head == 0");
    ctx.push_assume("count_val", "count == 3");

    // First dequeue reads buf[head] = buf[0] = 10
    ctx.push_assert("fifo_first", "buf.index(0) == 10");
    // Second dequeue would read buf[1] = 20
    ctx.push_assert("fifo_second", "buf.index(1) == 20");
    // Third dequeue would read buf[2] = 30
    ctx.push_assert("fifo_third", "buf.index(2) == 30");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65d: FIFO concrete trace should verify, got: {:?}",
        result,
    );
}

/// Tier 65d: FIFO — wrapped enqueue/dequeue preserves order.
/// head=3, cap=5: enqueue 10,20,30 writes at indices 3,4,0.
/// Dequeue reads 3,4,0 in that order.
#[test]
fn test_vt_tier65d_fifo_wrapped_order() {
    let mut ctx = VerificationContext::new();
    // buf[3]=10, buf[4]=20, buf[0]=30 (wrapped)
    assume_seq_i64(&mut ctx, "buf", &[30, 0, 0, 10, 20]);

    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.push_assume("cap_val", "cap == 5");
    ctx.push_assume("head_val", "head == 3");
    ctx.push_assume("count_val", "count == 3");

    // First dequeue: buf[head] = buf[3] = 10
    ctx.push_assert("fifo_first", "buf.index(3) == 10");
    // Second dequeue: buf[(3+1)%5] = buf[4] = 20
    ctx.push_assert("fifo_second", "buf.index(4) == 20");
    // Third dequeue: buf[(4+1)%5] = buf[0] = 30 (wrapped!)
    ctx.push_assert("fifo_third", "buf.index(0) == 30");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 65d: FIFO wrapped order should verify, got: {:?}",
        result,
    );
}
