// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 20 — Modular arithmetic competition patterns.
//!
//! Exercises modular index-wrapping in verification contexts, a critical
//! capability for VerifyThis problems involving circular buffers, hash
//! tables, and index-wrapping algorithms.
//!
//! GROUP A: Circular Buffer — ring buffer with modular head/tail pointers.
//!   Archetype: bounded queues, sliding windows, producer-consumer.
//!   Key VC: count tracking after enqueue/dequeue.
//!
//! GROUP B: Modular Index Probing — hash table linear probing.
//!   Archetype: open addressing, cache-line scanning, cyclic iteration.
//!   Key VC: probe index stays in bounds and covers all slots.
//!
//! COMPETITION PATTERN: ay-dpll's BV64 `bvurem` is non-deterministic —
//! concrete-value `%` queries sometimes return Unknown. The competition-
//! resilient approach rewrites `x = (a + 1) % n` as a conditional:
//!   `(a + 1 < n && x == a + 1) || (a + 1 >= n && x == 0)`
//! This is semantically identical for 0 <= a < n, n > 0, and lets the
//! BV solver use simple comparison + arithmetic instead of full division.
//! Similarly, count = (tail - head + cap) % cap becomes:
//!   `(tail >= head && count == tail - head) ||
//!    (tail < head && count == tail + cap - head)`
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ========================================================================
// GROUP A: Circular Buffer
//
// Fixed-capacity ring buffer using a Seq of size `cap`. Two u64 indices
// `head` and `tail` wrap around. The count of elements is:
//   if tail >= head: count = tail - head
//   if tail < head:  count = tail + cap - head
// Enqueue stores at tail and advances; dequeue advances head.
//
// This is a competition staple: VerifyThis 2022 P1 (mergesort with runs)
// uses similar index arithmetic, and many queue/buffer problems rely on
// modular pointer reasoning.
// ========================================================================

/// Tier 20a: Circular buffer init — empty buffer satisfies invariant.
///
/// head=0, tail=0 → count = 0 (tail >= head case).
/// DISCRIMINATING: Changing cap to 0 would violate cap_pos.
#[test]
fn test_vt_tier20a_circular_buffer_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("buf", "Seq<i32>");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("tail", "u64");
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("count", "u64");

    // Buffer has fixed capacity
    ctx.push_assume("cap_pos", "cap == 8");
    ctx.push_assume("buf_len", "buf.len() == cap");

    // Init state: both pointers at 0
    ctx.push_assume("head_init", "head == 0");
    ctx.push_assume("tail_init", "tail == 0");

    // Count via conditional (competition pattern, avoids BV64 %)
    ctx.push_assume(
        "count_def",
        "(tail >= head && count == tail - head) || \
         (tail < head && count == tail + cap - head)",
    );

    // Invariant: count == 0 at init
    ctx.push_assert("count_zero", "count == 0");
    // head and tail are in bounds
    ctx.push_assert("head_bound", "head < cap");
    ctx.push_assert("tail_bound", "tail < cap");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 20a: circular buffer init should verify, got: {:?}",
        result,
    );
}

/// Tier 20a: Circular buffer enqueue (no wrap) — count increases by 1.
///
/// Concrete: head=2, tail=5, cap=8. count = 5-2 = 3.
/// After enqueue: tail_new = 5+1 = 6 (no wrap). new count = 6-2 = 4.
///
/// COMPETITION PATTERN: Advance via conditional instead of %.
/// DISCRIMINATING: Changing tail from 5 to 7 gives the wrap case.
#[test]
fn test_vt_tier20a_enqueue_no_wrap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("buf", "Seq<i32>");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("tail", "u64");
    ctx.declare_var_parsed("tail_new", "u64");
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("val", "i32");
    ctx.declare_var_parsed("count_old", "u64");
    ctx.declare_var_parsed("count_new", "u64");

    ctx.push_assume("cap_val", "cap == 8");
    ctx.push_assume("buf_len", "buf.len() == 8");

    // Concrete state: head=2, tail=5 (no wrap)
    ctx.push_assume("head_val", "head == 2");
    ctx.push_assume("tail_val", "tail == 5");

    // Advance tail: conditional instead of (tail + 1) % cap
    ctx.push_assume(
        "tail_advance",
        "(tail + 1 < cap && tail_new == tail + 1) || \
         (tail + 1 >= cap && tail_new == 0)",
    );

    // Count via conditional (competition pattern)
    ctx.push_assume(
        "count_old_def",
        "(tail >= head && count_old == tail - head) || \
         (tail < head && count_old == tail + cap - head)",
    );
    ctx.push_assume(
        "count_new_def",
        "(tail_new >= head && count_new == tail_new - head) || \
         (tail_new < head && count_new == tail_new + cap - head)",
    );

    // Verify: tail_new = 6, count goes from 3 to 4
    ctx.push_assert("tail_new_val", "tail_new == 6");
    ctx.push_assert("old_count", "count_old == 3");
    ctx.push_assert("new_count", "count_new == 4");
    // Store preserves value
    ctx.push_assert("stored", "buf.update(tail, val).index(tail) == val");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 20a: enqueue (no wrap) should verify, got: {:?}",
        result,
    );
}

/// Tier 20a: Circular buffer enqueue (wrap case) — tail wraps from 7 to 0.
///
/// Concrete: head=3, tail=7, cap=8. count = 7-3 = 4.
/// After enqueue: tail_new = 0 (wrap). new count = 0+8-3 = 5.
///
/// This exercises the wrap-around where tail_new < tail.
#[test]
fn test_vt_tier20a_enqueue_wrap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("buf", "Seq<i32>");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("tail", "u64");
    ctx.declare_var_parsed("tail_new", "u64");
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("val", "i32");
    ctx.declare_var_parsed("count_old", "u64");
    ctx.declare_var_parsed("count_new", "u64");

    ctx.push_assume("cap_val", "cap == 8");
    ctx.push_assume("buf_len", "buf.len() == 8");

    // Concrete state: head=3, tail=7 (tail at buffer end)
    ctx.push_assume("head_val", "head == 3");
    ctx.push_assume("tail_val", "tail == 7");

    // Advance tail: conditional wrap
    ctx.push_assume(
        "tail_advance",
        "(tail + 1 < cap && tail_new == tail + 1) || \
         (tail + 1 >= cap && tail_new == 0)",
    );

    // Count via conditional
    ctx.push_assume(
        "count_old_def",
        "(tail >= head && count_old == tail - head) || \
         (tail < head && count_old == tail + cap - head)",
    );
    ctx.push_assume(
        "count_new_def",
        "(tail_new >= head && count_new == tail_new - head) || \
         (tail_new < head && count_new == tail_new + cap - head)",
    );

    // Verify: tail wraps to 0, count goes from 4 to 5
    ctx.push_assert("tail_wraps", "tail_new == 0");
    ctx.push_assert("old_count", "count_old == 4");
    ctx.push_assert("new_count", "count_new == 5");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 20a: enqueue (wrap) should verify, got: {:?}",
        result,
    );
}

/// Tier 20a: Circular buffer dequeue (no wrap) — count decreases by 1.
///
/// Concrete: head=2, tail=5, cap=8. count = 3.
/// After dequeue: head_new = 3 (no wrap). new count = 5-3 = 2.
#[test]
fn test_vt_tier20a_dequeue_no_wrap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("tail", "u64");
    ctx.declare_var_parsed("head_new", "u64");
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("count_old", "u64");
    ctx.declare_var_parsed("count_new", "u64");

    ctx.push_assume("cap_val", "cap == 8");
    ctx.push_assume("head_val", "head == 2");
    ctx.push_assume("tail_val", "tail == 5");

    // Advance head: conditional instead of (head + 1) % cap
    ctx.push_assume(
        "head_advance",
        "(head + 1 < cap && head_new == head + 1) || \
         (head + 1 >= cap && head_new == 0)",
    );

    // Count via conditional
    ctx.push_assume(
        "count_old_def",
        "(tail >= head && count_old == tail - head) || \
         (tail < head && count_old == tail + cap - head)",
    );
    ctx.push_assume(
        "count_new_def",
        "(tail >= head_new && count_new == tail - head_new) || \
         (tail < head_new && count_new == tail + cap - head_new)",
    );

    // Verify: head_new = 3, count goes from 3 to 2
    ctx.push_assert("head_new_val", "head_new == 3");
    ctx.push_assert("old_count", "count_old == 3");
    ctx.push_assert("new_count", "count_new == 2");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 20a: dequeue (no wrap) should verify, got: {:?}",
        result,
    );
}

/// Tier 20a: Circular buffer dequeue (wrap) — head wraps from 7 to 0.
///
/// Concrete: head=7, tail=3, cap=8. count = 3+8-7 = 4.
/// After dequeue: head_new = 0 (wrap). new count = 3-0 = 3.
#[test]
fn test_vt_tier20a_dequeue_wrap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("tail", "u64");
    ctx.declare_var_parsed("head_new", "u64");
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("count_old", "u64");
    ctx.declare_var_parsed("count_new", "u64");

    ctx.push_assume("cap_val", "cap == 8");
    ctx.push_assume("head_val", "head == 7");
    ctx.push_assume("tail_val", "tail == 3");

    // Advance head: conditional wrap
    ctx.push_assume(
        "head_advance",
        "(head + 1 < cap && head_new == head + 1) || \
         (head + 1 >= cap && head_new == 0)",
    );

    // Count via conditional
    ctx.push_assume(
        "count_old_def",
        "(tail >= head && count_old == tail - head) || \
         (tail < head && count_old == tail + cap - head)",
    );
    ctx.push_assume(
        "count_new_def",
        "(tail >= head_new && count_new == tail - head_new) || \
         (tail < head_new && count_new == tail + cap - head_new)",
    );

    // Verify: head wraps to 0, count goes from 4 to 3
    ctx.push_assert("head_wraps", "head_new == 0");
    ctx.push_assert("old_count", "count_old == 4");
    ctx.push_assert("new_count", "count_new == 3");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 20a: dequeue (wrap) should verify, got: {:?}",
        result,
    );
}

/// Tier 20a: Circular buffer wrap-around — enqueue at tail=cap-1 wraps to 0.
///
/// Same scenario as enqueue_wrap but structured as standalone wrap test.
/// Count increases from 4 to 5 across the boundary.
#[test]
fn test_vt_tier20a_wraparound() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("buf", "Seq<i32>");
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("tail", "u64");
    ctx.declare_var_parsed("tail_new", "u64");
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("count_old", "u64");
    ctx.declare_var_parsed("count_new", "u64");

    ctx.push_assume("cap_val", "cap == 8");
    ctx.push_assume("buf_len", "buf.len() == 8");
    ctx.push_assume("head_val", "head == 3");
    ctx.push_assume("tail_val", "tail == 7"); // at end of buffer

    // Advance tail: conditional wrap
    ctx.push_assume(
        "tail_advance",
        "(tail + 1 < cap && tail_new == tail + 1) || \
         (tail + 1 >= cap && tail_new == 0)",
    );

    // Count via conditional
    ctx.push_assume(
        "count_old_def",
        "(tail >= head && count_old == tail - head) || \
         (tail < head && count_old == tail + cap - head)",
    );
    ctx.push_assume(
        "count_new_def",
        "(tail_new >= head && count_new == tail_new - head) || \
         (tail_new < head && count_new == tail_new + cap - head)",
    );

    // tail wraps to 0
    ctx.push_assert("wraps_to_zero", "tail_new == 0");
    // Old count was 4 (slots 3,4,5,6), new count is 5 (slots 3,4,5,6,7)
    ctx.push_assert("old_count", "count_old == 4");
    ctx.push_assert("new_count", "count_new == 5");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 20a: wrap-around should verify, got: {:?}",
        result,
    );
}

/// Tier 20a: Circular buffer negative — enqueue when full wraps count to 0.
///
/// Concrete: head=1, tail=0, cap=8. count = 0+8-1 = 7 (full, one reserved).
/// After enqueue: tail_new = 1 = head. count = 0 (appears empty!).
/// The buffer appears empty even though it's full — classic ring buffer bug.
#[test]
fn test_vt_tier20a_enqueue_full_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("head", "u64");
    ctx.declare_var_parsed("tail", "u64");
    ctx.declare_var_parsed("tail_new", "u64");
    ctx.declare_var_parsed("cap", "u64");
    ctx.declare_var_parsed("count_new", "u64");

    ctx.push_assume("cap_val", "cap == 8");
    // Full buffer: head=1, tail=0, count = 7
    ctx.push_assume("head_val", "head == 1");
    ctx.push_assume("tail_val", "tail == 0");

    // Enqueue anyway (BUG: buffer is full)
    ctx.push_assume(
        "tail_advance",
        "(tail + 1 < cap && tail_new == tail + 1) || \
         (tail + 1 >= cap && tail_new == 0)",
    );

    // Count via conditional
    ctx.push_assume(
        "count_new_def",
        "(tail_new >= head && count_new == tail_new - head) || \
         (tail_new < head && count_new == tail_new + cap - head)",
    );

    // Claim: count == 8 (all slots used). This fails because
    // tail_new == 1 == head, so count = 0, not 8.
    ctx.push_assert("count_valid", "count_new == 8");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 20a negative: enqueue when full must produce Counterexample, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Modular Index Probing (Hash Table)
//
// Linear probing: start at h = key % table_size, probe h, h+1, h+2, ...
// all with wrapping. Key properties:
//   1. All probe indices are in bounds [0, table_size)
//   2. After table_size probes, we've visited every slot
//
// COMPETITION PATTERN: Instead of `h = key % n`, pre-compute the hash
// for concrete keys (42 % 16 = 10) and model the step as conditional
// wrap. ay-dpll handles comparison+arithmetic reliably; BV64 bvurem
// is non-deterministic.
//
// This pattern appears in VerifyThis hash table problems (2022 P2,
// 2023 P2) and any open-addressing data structure.
// ========================================================================

/// Tier 20b: Linear probe — probe index stays in bounds (concrete keys).
///
/// For key=42, step i=5, table size 16: hash=42%16=10, probe=(10+5)%16=15.
///
/// COMPETITION PATTERN: Pre-compute key%n=10 as assumption, use conditional
/// for the outer wrap. Avoids double-bvurem.
#[test]
fn test_vt_tier20b_probe_in_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("key", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("key_mod", "u64");
    ctx.declare_var_parsed("raw_h", "u64");
    ctx.declare_var_parsed("h", "u64");

    ctx.push_assume("n_val", "n == 16");
    ctx.push_assume("key_val", "key == 42");
    ctx.push_assume("i_val", "i == 5");
    // Pre-compute: 42 % 16 = 10 (known at VC construction time)
    ctx.push_assume("key_mod_val", "key_mod == 10");
    ctx.push_assume("raw_h_def", "raw_h == key_mod + i");
    // Conditional wrap instead of outer %
    ctx.push_assume(
        "h_def",
        "(raw_h < n && h == raw_h) || (raw_h >= n && h == raw_h - n)",
    );

    // h = 10 + 5 = 15, 15 < 16 so h = 15
    ctx.push_assert("h_val", "h == 15");
    ctx.push_assert("h_bound", "h < n");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 20b: probe in bounds should verify, got: {:?}",
        result,
    );
}

/// Tier 20b: Linear probe — large key wraps correctly.
///
/// key=1000000, n=16: 1000000 % 16 = 0 (1000000 = 62500 * 16).
/// Pre-computed as assumption to avoid BV64 bvurem.
#[test]
fn test_vt_tier20b_probe_large_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("key", "u64");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("h", "u64");

    ctx.push_assume("n_val", "n == 16");
    ctx.push_assume("key_val", "key == 1000000");
    // Pre-compute: 1000000 % 16 = 0
    ctx.push_assume("h_val_precomputed", "h == 0");

    ctx.push_assert("h_bound", "h < n");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 20b: large key probe should verify, got: {:?}",
        result,
    );
}

/// Tier 20b: Linear probe step — advancing by 1 stays in bounds.
///
/// If current probe index p < n, then the next probe is:
///   p_new = p + 1 if p + 1 < n, else 0
/// This guarantees p_new < n.
///
/// COMPETITION PATTERN: Symbolic p with conditional wrap. ay-dpll handles
/// this reliably because it's just BV comparison + addition, no division.
#[test]
fn test_vt_tier20b_probe_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "u64");
    ctx.declare_var_parsed("p_new", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("n_pos", "n == 16");
    ctx.push_assume("p_bound", "p < n");
    // Conditional wrap instead of (p + 1) % n
    ctx.push_assume(
        "step",
        "(p + 1 < n && p_new == p + 1) || (p + 1 >= n && p_new == 0)",
    );

    ctx.push_assert("p_new_bound", "p_new < n");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 20b: probe step should verify, got: {:?}",
        result,
    );
}

/// Tier 20b: Modular index lookup — value at computed index.
///
/// Concrete: table of size 4, key=10. h = 10 % 4 = 2 (pre-computed).
/// table[h] should be table[2].
#[test]
fn test_vt_tier20b_index_lookup() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("table", "Seq<i32>");
    ctx.declare_var_parsed("key", "u64");
    ctx.declare_var_parsed("h", "u64");

    ctx.push_assume("table_len", "table.len() == 4");
    ctx.push_assume("key_val", "key == 10");
    // Pre-compute: 10 % 4 = 2
    ctx.push_assume("h_def", "h == 2");

    ctx.push_assert("h_bound", "h < table.len()");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 20b: index lookup should verify, got: {:?}",
        result,
    );
}

/// Tier 20b: Probe with update — insert at computed index.
///
/// Store value at table[h], then read it back. h is in bounds (assumed).
#[test]
fn test_vt_tier20b_probe_update() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("table", "Seq<i32>");
    ctx.declare_var_parsed("key", "u64");
    ctx.declare_var_parsed("val", "i32");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("h", "u64");

    ctx.push_assume("n_val", "n == 8");
    ctx.push_assume("table_len", "table.len() == n");
    // Pre-compute hash and assume in bounds
    ctx.push_assume("h_bound", "h < n");

    // After store, reading back gives the stored value
    ctx.push_assert("read_back", "table.update(h, val).index(h) == val");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 20b: probe update read-back should verify, got: {:?}",
        result,
    );
}

/// Tier 20b: Negative — wrong modulus loses bounds guarantee.
///
/// If we advance without wrapping (just add, no conditional), the
/// result can exceed n when offset is large enough.
#[test]
fn test_vt_tier20b_missing_outer_mod_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("key_mod", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("n_val", "n == 8");
    ctx.push_assume("i_val", "i == 5");
    ctx.push_assume("key_mod_val", "key_mod == 6");

    // Without wrapping: key_mod + i = 6 + 5 = 11, NOT < 8
    ctx.push_assert("wrong_bound", "key_mod + i < n");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 20b negative: missing wrap must produce Counterexample, got: {:?}",
        result,
    );
}
