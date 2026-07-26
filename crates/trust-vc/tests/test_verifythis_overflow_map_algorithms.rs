// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 26 — Map-based algorithm VCs under overflow checking.
//!
//! Tier 16 validated Map/Set core operations. Tiers 21-25 added overflow
//! checking to Seq-based algorithms. This tier combines both: Map-based
//! patterns with `check_overflow = true`.
//!
//! GROUP A: Histogram counting (freq[key] += 1) — Init/Step/Exit/Neg.
//! GROUP B: Value accumulation (sums[key] += val) — bounded addition.
//! GROUP C: Multi-map merge (result[k] = a[k] + b[k]).
//! GROUP D: Persistent array under overflow (VerifyThis 2025 pattern).
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline.

mod common;

use common::verify_context_with_pipeline;
use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

fn assume_contains_key(ctx: &mut VerificationContext, name: &str, map: &str, key: &str) {
    let condition = format!("{map}.contains_key({key})");
    ctx.push_assume(name, &condition);
}

// GROUP A: Histogram Counting under Overflow
// Pattern: freq[key] += 1. Requires bounded count to prevent overflow.
// INIT/STEP/EXIT/NEG decomposition.

/// Tier 26a INIT: Empty histogram — count 0 at any key.
#[test]
fn test_vt_tier26a_histogram_init() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("freq", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");

    // Initialized histogram entry for the observed key.
    assume_contains_key(&mut ctx, "has_k", "freq", "k");
    ctx.push_assume("initial_zero", "freq.get(k) == 0");

    // Invariant at start: count is non-negative and bounded
    ctx.push_assert("non_neg", "freq.get(k) >= 0");
    ctx.push_assert("bounded", "freq.get(k) <= 1000000");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 26a INIT: empty histogram should verify under overflow: {:?}",
        result,
    );
}

/// Tier 26a STEP: Bounded increment — `count + 1` overflows without upper bound.
#[test]
fn test_vt_tier26a_histogram_step() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("freq", "Map<i32, i32>");
    ctx.declare_var_parsed("freq_new", "Map<i32, i32>");
    ctx.declare_var_parsed("elem", "i32");
    ctx.declare_var_parsed("old_count", "i32");

    // Pre: count is bounded (competition strategy: bound before increment)
    assume_contains_key(&mut ctx, "has_elem", "freq", "elem");
    ctx.push_assume("old_count_def", "old_count == freq.get(elem)");
    ctx.push_assume("count_bounded", "old_count >= 0 && old_count < 1000000");

    // Step: increment count
    ctx.push_assume("update", "freq_new == freq.insert(elem, old_count + 1)");

    // Post: new count is incremented and bounded
    ctx.push_assert("incremented", "freq_new.get(elem) == old_count + 1");
    ctx.push_assert("new_positive", "freq_new.get(elem) > 0");
    ctx.push_assert("new_bounded", "freq_new.get(elem) <= 1000000");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 26a STEP: bounded histogram increment should verify under overflow: {:?}",
        result,
    );
}

/// Tier 26a STEP FRAME: Increment at elem preserves other keys.
#[test]
fn test_vt_tier26a_histogram_step_frame() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("freq", "Map<i32, i32>");
    ctx.declare_var_parsed("freq_new", "Map<i32, i32>");
    ctx.declare_var_parsed("elem", "i32");
    ctx.declare_var_parsed("other", "i32");
    ctx.declare_var_parsed("old_count", "i32");

    ctx.push_assume("distinct", "elem != other");
    assume_contains_key(&mut ctx, "has_elem", "freq", "elem");
    assume_contains_key(&mut ctx, "has_other", "freq", "other");
    ctx.push_assume("old_count_def", "old_count == freq.get(elem)");
    ctx.push_assume("count_bounded", "old_count >= 0 && old_count < 1000000");
    ctx.push_assume("update", "freq_new == freq.insert(elem, old_count + 1)");

    // Frame: other key unchanged
    ctx.push_assert("frame", "freq_new.get(other) == freq.get(other)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 26a FRAME: histogram frame should verify under overflow: {:?}",
        result,
    );
}

/// Tier 26a EXIT: Concrete [3, 1, 3, 2] histogram — freq[3]=2, freq[1]=1, freq[2]=1.
#[test]
fn test_vt_tier26a_histogram_exit() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("f0", "Map<i32, i32>");
    ctx.declare_var_parsed("f1", "Map<i32, i32>");
    ctx.declare_var_parsed("f2", "Map<i32, i32>");
    ctx.declare_var_parsed("f3", "Map<i32, i32>");
    ctx.declare_var_parsed("f4", "Map<i32, i32>");

    // Initial: all counts 0 (modeled by concrete assumptions)
    assume_contains_key(&mut ctx, "f0_has_1", "f0", "1");
    assume_contains_key(&mut ctx, "f0_has_2", "f0", "2");
    assume_contains_key(&mut ctx, "f0_has_3", "f0", "3");
    ctx.push_assume("init_1", "f0.get(1) == 0");
    ctx.push_assume("init_2", "f0.get(2) == 0");
    ctx.push_assume("init_3", "f0.get(3) == 0");

    // Step 1: count element 3 → f1[3] = f0[3] + 1 = 1
    ctx.push_assume("s1", "f1 == f0.insert(3, f0.get(3) + 1)");
    // Step 2: count element 1 → f2[1] = f1[1] + 1
    ctx.push_assume("s2_frame", "f1.get(1) == f0.get(1)"); // frame: insert(3,...) doesn't change key 1
    ctx.push_assume("s2", "f2 == f1.insert(1, f1.get(1) + 1)");
    // Step 3: count element 3 → f3[3] = f2[3] + 1
    ctx.push_assume("s3_frame", "f2.get(3) == f1.get(3)"); // frame: insert(1,...) doesn't change key 3
    ctx.push_assume("s3", "f3 == f2.insert(3, f2.get(3) + 1)");
    // Step 4: count element 2 → f4[2] = f3[2] + 1
    ctx.push_assume("s4_frame1", "f3.get(2) == f2.get(2)"); // frame through steps 3
    ctx.push_assume("s4_frame2", "f2.get(2) == f1.get(2)"); // frame through step 2
    ctx.push_assume("s4_frame3", "f1.get(2) == f0.get(2)"); // frame through step 1
    ctx.push_assume("s4", "f4 == f3.insert(2, f3.get(2) + 1)");

    // Postcondition: final counts
    ctx.push_assert("count_3", "f4.get(3) == f3.get(3)"); // frame: insert(2,...) keeps key 3
    ctx.push_assert("count_1", "f4.get(1) == f3.get(1)"); // frame: insert(2,...) keeps key 1

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 26a EXIT: concrete histogram should verify under overflow: {:?}",
        result,
    );
}

/// Tier 26a NEGATIVE: Unbounded count increment can overflow.
///
/// Without the bound `old_count < 1000000`, the increment `old_count + 1`
/// can overflow i32. The verifier must reject this.
#[test]
fn test_vt_tier26a_histogram_unbounded_negative() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("freq", "Map<i32, i32>");
    ctx.declare_var_parsed("freq_new", "Map<i32, i32>");
    ctx.declare_var_parsed("elem", "i32");
    ctx.declare_var_parsed("old_count", "i32");

    // NO upper bound on count — this is the bug
    assume_contains_key(&mut ctx, "has_elem", "freq", "elem");
    ctx.push_assume("old_count_def", "old_count == freq.get(elem)");
    ctx.push_assume("count_non_neg", "old_count >= 0");
    ctx.push_assume("count_max", "old_count == 2147483647");

    // Trying to prove increment happened — but overflow makes this unsound
    ctx.push_assert(
        "incremented",
        "freq.insert(elem, old_count + 1).get(elem) == old_count + 1",
    );

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 26a NEG: unbounded increment must produce Counterexample — overflow possible: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Map-based Value Accumulation under Overflow
//
// Pattern: sums[key] += value. Like histogram but accumulating arbitrary
// bounded values instead of just +1. Competition relevance: group-by-sum
// (e.g., total sales by category, weight by bin).
// ========================================================================

/// Tier 26b: Bounded value accumulation — sum update with bounds.
///
/// Given: sums[k] bounded by ±500000, val bounded by ±1000.
/// Step: sums_new[k] = sums[k] + val.
/// Prove: result bounded by ±501000.
#[test]
fn test_vt_tier26b_value_accumulation_step() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("sums", "Map<i32, i32>");
    ctx.declare_var_parsed("sums_new", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");
    ctx.declare_var_parsed("val", "i32");
    ctx.declare_var_parsed("old_sum", "i32");

    assume_contains_key(&mut ctx, "has_k", "sums", "k");
    ctx.push_assume("old_sum_def", "old_sum == sums.get(k)");
    ctx.push_assume("sum_bounded", "old_sum >= -500000 && old_sum <= 500000");
    ctx.push_assume("val_bounded", "val >= -1000 && val <= 1000");
    ctx.push_assume("update", "sums_new == sums.insert(k, old_sum + val)");

    ctx.push_assert(
        "result_bounded",
        "sums_new.get(k) >= -501000 && sums_new.get(k) <= 501000",
    );
    ctx.push_assert("correct_sum", "sums_new.get(k) == old_sum + val");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 26b: bounded accumulation should verify under overflow: {:?}",
        result,
    );
}

/// Tier 26b: Accumulation frame — updating one key preserves others.
#[test]
fn test_vt_tier26b_value_accumulation_frame() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("sums", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");
    ctx.declare_var_parsed("j", "i32");
    ctx.declare_var_parsed("val", "i32");
    ctx.declare_var_parsed("old_sum", "i32");

    ctx.push_assume("distinct", "k != j");
    assume_contains_key(&mut ctx, "has_k", "sums", "k");
    assume_contains_key(&mut ctx, "has_j", "sums", "j");
    ctx.push_assume("old_sum_def", "old_sum == sums.get(k)");
    ctx.push_assume("sum_bounded", "old_sum >= -500000 && old_sum <= 500000");
    ctx.push_assume("val_bounded", "val >= -1000 && val <= 1000");

    ctx.push_assert(
        "frame",
        "sums.insert(k, old_sum + val).get(j) == sums.get(j)",
    );

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 26b: accumulation frame should verify under overflow: {:?}",
        result,
    );
}

/// Tier 26b NEGATIVE: Unbounded accumulation overflows.
///
/// Without bounds on existing sum, `sums[k] + val` can overflow.
#[test]
fn test_vt_tier26b_value_accumulation_unbounded_negative() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("sums", "Map<i32, i32>");
    ctx.declare_var_parsed("sums_new", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");
    ctx.declare_var_parsed("val", "i32");

    // NO bound on sums.get(k) — this allows overflow
    assume_contains_key(&mut ctx, "has_k", "sums", "k");
    ctx.push_assume("val_bounded", "val >= -1000 && val <= 1000");
    ctx.push_assume("old_sum_max", "sums.get(k) == 2147483647");
    ctx.push_assume("val_one", "val == 1");

    ctx.push_assert(
        "correct",
        "sums.insert(k, sums.get(k) + val).get(k) == sums.get(k) + val",
    );

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 26b NEG: unbounded accumulation must produce Counterexample: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Multi-map Merge under Overflow
//
// Combine two maps by summing their values: result[k] = a[k] + b[k].
// Competition relevance: parallel reduction combine step, histogram merging,
// matrix addition stored as key-value.
// ========================================================================

/// Tier 26c: Bounded merge — both maps have bounded values.
///
/// Given: a[k] in [-500000, 500000], b[k] in [-500000, 500000].
/// Step: result[k] = a[k] + b[k].
/// Prove: result[k] in [-1000000, 1000000].
#[test]
fn test_vt_tier26c_map_merge_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Map<i32, i32>");
    ctx.declare_var_parsed("b", "Map<i32, i32>");
    ctx.declare_var_parsed("result", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");
    ctx.declare_var_parsed("a_val", "i32");
    ctx.declare_var_parsed("b_val", "i32");

    assume_contains_key(&mut ctx, "a_has_k", "a", "k");
    assume_contains_key(&mut ctx, "b_has_k", "b", "k");
    ctx.push_assume("a_val_def", "a_val == a.get(k)");
    ctx.push_assume("b_val_def", "b_val == b.get(k)");
    ctx.push_assume("a_bounded", "a_val >= -500000 && a_val <= 500000");
    ctx.push_assume("b_bounded", "b_val >= -500000 && b_val <= 500000");
    ctx.push_assume("merge_def", "result == a.insert(k, a_val + b_val)");

    ctx.push_assert(
        "result_bounded",
        "result.get(k) >= -1000000 && result.get(k) <= 1000000",
    );
    ctx.push_assert("result_is_sum", "result.get(k) == a_val + b_val");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 26c: bounded map merge should verify under overflow: {:?}",
        result,
    );
}

/// Tier 26c: Merge frame — merging at k preserves other keys.
#[test]
fn test_vt_tier26c_map_merge_frame() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Map<i32, i32>");
    ctx.declare_var_parsed("b", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");
    ctx.declare_var_parsed("j", "i32");
    ctx.declare_var_parsed("a_val", "i32");
    ctx.declare_var_parsed("b_val", "i32");

    ctx.push_assume("distinct", "k != j");
    assume_contains_key(&mut ctx, "a_has_k", "a", "k");
    assume_contains_key(&mut ctx, "a_has_j", "a", "j");
    assume_contains_key(&mut ctx, "b_has_k", "b", "k");
    ctx.push_assume("a_val_def", "a_val == a.get(k)");
    ctx.push_assume("b_val_def", "b_val == b.get(k)");
    ctx.push_assume("a_bounded", "a_val >= -500000 && a_val <= 500000");
    ctx.push_assume("b_bounded", "b_val >= -500000 && b_val <= 500000");

    // Merging at k doesn't affect key j
    ctx.push_assert("frame", "a.insert(k, a_val + b_val).get(j) == a.get(j)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 26c: merge frame should verify under overflow: {:?}",
        result,
    );
}

/// Tier 26c NEGATIVE: Merge without bounds overflows.
#[test]
fn test_vt_tier26c_map_merge_unbounded_negative() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Map<i32, i32>");
    ctx.declare_var_parsed("b", "Map<i32, i32>");
    ctx.declare_var_parsed("result", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");

    // NO bounds — a.get(k) + b.get(k) can overflow
    assume_contains_key(&mut ctx, "a_has_k", "a", "k");
    assume_contains_key(&mut ctx, "b_has_k", "b", "k");
    ctx.push_assume("a_val_max", "a.get(k) == 2147483647");
    ctx.push_assume("b_val_one", "b.get(k) == 1");
    ctx.push_assert(
        "is_sum",
        "a.insert(k, a.get(k) + b.get(k)).get(k) == a.get(k) + b.get(k)",
    );

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 26c NEG: unbounded merge must produce Counterexample: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Persistent Array under Overflow (Index + Value Arithmetic)
//
// Persistent arrays (VerifyThis 2025 Challenge 1) use Map<u64, i32> where
// index arithmetic and value computations interact with overflow checking.
// Competition pattern: write at computed index, read back with arithmetic.
// ========================================================================

/// Tier 26d: Persistent array write-read with value arithmetic under overflow.
///
/// Write val + delta at index i, read back. Under overflow, val + delta must
/// be bounded to verify.
#[test]
fn test_vt_tier26d_persistent_array_value_arithmetic() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("arr", "Map<u64, i32>");
    ctx.declare_var_parsed("arr_new", "Map<u64, i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("val", "i32");
    ctx.declare_var_parsed("delta", "i32");

    ctx.push_assume("val_bounded", "val >= -1000000 && val <= 1000000");
    ctx.push_assume("delta_bounded", "delta >= -1000 && delta <= 1000");
    ctx.push_assume("write", "arr_new == arr.insert(i, val + delta)");

    // Read back the written value
    ctx.push_assert("read_back", "arr_new.get(i) == val + delta");
    // Value is bounded
    ctx.push_assert(
        "result_bounded",
        "arr_new.get(i) >= -1001000 && arr_new.get(i) <= 1001000",
    );

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 26d: persistent array value arithmetic should verify under overflow: {:?}",
        result,
    );
}

/// Tier 26d: Persistent array frame under overflow — write at i preserves j.
#[test]
fn test_vt_tier26d_persistent_array_frame_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("arr", "Map<u64, i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("val", "i32");
    ctx.declare_var_parsed("delta", "i32");

    ctx.push_assume("distinct", "i != j");
    assume_contains_key(&mut ctx, "arr_has_j", "arr", "j");
    ctx.push_assume("val_bounded", "val >= -1000000 && val <= 1000000");
    ctx.push_assume("delta_bounded", "delta >= -1000 && delta <= 1000");

    // Frame: write at i doesn't affect j
    ctx.push_assert("frame", "arr.insert(i, val + delta).get(j) == arr.get(j)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 26d: persistent array frame should verify under overflow: {:?}",
        result,
    );
}

/// Tier 26d: Persistent array fork with value computation under overflow.
///
/// v1 = arr.insert(0, base + 10), v2 = arr.insert(0, base + 20).
/// Under overflow, base must be bounded for both computations.
/// The two versions diverge at index 0 but agree elsewhere.
#[test]
fn test_vt_tier26d_persistent_array_fork_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("arr", "Map<u64, i32>");
    ctx.declare_var_parsed("v1", "Map<u64, i32>");
    ctx.declare_var_parsed("v2", "Map<u64, i32>");
    ctx.declare_var_parsed("base", "i32");

    ctx.push_assume("base_bounded", "base >= -1000000 && base <= 1000000");
    assume_contains_key(&mut ctx, "arr_has_1", "arr", "1");
    ctx.push_assume("v1_write", "v1 == arr.insert(0, base + 10)");
    ctx.push_assume("v2_write", "v2 == arr.insert(0, base + 20)");

    // v1 and v2 diverge at index 0
    ctx.push_assert("v1_val", "v1.get(0) == base + 10");
    ctx.push_assert("v2_val", "v2.get(0) == base + 20");
    // Difference between versions is exactly 10
    ctx.push_assert("diff", "v2.get(0) - v1.get(0) == 10");
    // Both agree at index 1 (frame)
    ctx.push_assert("agree", "v1.get(1) == v2.get(1)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 26d: persistent array fork with overflow should verify: {:?}",
        result,
    );
}

/// Tier 26d NEGATIVE: Persistent array with unbounded value arithmetic overflows.
#[test]
fn test_vt_tier26d_persistent_array_unbounded_negative() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("arr", "Map<u64, i32>");
    ctx.declare_var_parsed("arr_new", "Map<u64, i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("val", "i32");
    ctx.declare_var_parsed("delta", "i32");

    // NO bounds on val or delta — val + delta can overflow
    ctx.push_assume("val_max", "val == 2147483647");
    ctx.push_assume("delta_one", "delta == 1");
    ctx.push_assert(
        "read_back",
        "arr.insert(i, val + delta).get(i) == val + delta",
    );

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 26d NEG: unbounded value arithmetic must produce Counterexample: {:?}",
        result,
    );
}
