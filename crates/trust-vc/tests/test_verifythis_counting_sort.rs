// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 39 - Counting sort VCs.
//!
//! Counting sort appears in VerifyThis as a building block for:
//!   - Radix sort (2022 Mergesort with Runs used similar counting patterns)
//!   - Histogram / frequency analysis problems
//!   - Stability proofs (preserving relative order of equal elements)
//!
//! Key properties:
//!   1. count[v] == number of elements with value v in source
//!   2. output is sorted: output[i] <= output[i+1]
//!   3. output is a permutation of the input (total count preserved)
//!   4. weighted-sum conservation: sum(src) == Σ v*count[v]
//!
//! We model concrete small arrays and verify each property individually.
//! Expression-based prefix definitions and cross-phase conservation
//! assertions force the solver through genuine multi-step reasoning.
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

fn assume_seq_i64_exprs(ctx: &mut VerificationContext, name: &str, exprs: &[&str]) {
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(
        &format!("{name}_len"),
        &format!("{name}.len() == {}", exprs.len()),
    );
    for (index, expr) in exprs.iter().enumerate() {
        ctx.push_assume(
            &format!("{name}_{index}"),
            &format!("{name}.index({index}) == {expr}"),
        );
    }
}

fn occurrence_sum_expr(seq_name: &str, value: i64, len: usize) -> String {
    let terms = (0..len)
        .map(|index| format!("if {seq_name}.index({index}) == {value} {{ 1 }} else {{ 0 }}"))
        .collect::<Vec<_>>()
        .join(" + ");
    format!("({terms})")
}

// ========================================================================
// GROUP A: Counting phase correctness
// ========================================================================

/// Tier 39a: Count array correctly tallies frequency of each value.
///
/// Source array [2, 0, 2, 1, 0] with range [0..3).
/// count[0] = 2, count[1] = 1, count[2] = 2.
///
/// Exact tallies are derived from `src` using indicator sums, so the solver
/// must connect each `count[v]` to the positions where `src[i] == v`.
/// Weighted-sum conservation stays as a cross-check across all buckets.
#[test]
fn test_vt_tier39a_count_phase_tallies_frequencies() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "src", &[2, 0, 2, 1, 0]);
    assume_seq_i64(&mut ctx, "count", &[2, 1, 2]);
    let src_zeros = occurrence_sum_expr("src", 0, 5);
    let src_ones = occurrence_sum_expr("src", 1, 5);
    let src_twos = occurrence_sum_expr("src", 2, 5);

    ctx.push_assert(
        "count0_matches_src",
        &format!("count.index(0) == {src_zeros}"),
    );
    ctx.push_assert(
        "count1_matches_src",
        &format!("count.index(1) == {src_ones}"),
    );
    ctx.push_assert(
        "count2_matches_src",
        &format!("count.index(2) == {src_twos}"),
    );

    // Total count matches source length
    ctx.push_assert(
        "total_preserved",
        "count.index(0) + count.index(1) + count.index(2) == src.len()",
    );
    // Weighted-sum conservation: 0*count[0] + 1*count[1] + 2*count[2] == sum(src)
    // Since 0*count[0] vanishes: count[1] + count[2] + count[2] == sum(src)
    ctx.push_assert(
        "weighted_sum_conservation",
        "count.index(1) + count.index(2) + count.index(2) == src.index(0) + src.index(1) + src.index(2) + src.index(3) + src.index(4)",
    );
    // Each count is non-negative
    ctx.push_assert("c0_nonneg", "count.index(0) >= 0");
    ctx.push_assert("c1_nonneg", "count.index(1) >= 0");
    ctx.push_assert("c2_nonneg", "count.index(2) >= 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 39a: count phase should verify, got: {:?}",
        result,
    );
}

/// Tier 39b: Prefix-sum of counts yields placement offsets.
///
/// count = [2, 1, 2] -> prefix = [0, 2, 3].
/// Prefix defined via expressions from count, not concrete values.
/// Solver must expand count references to verify offset assertions.
#[test]
fn test_vt_tier39b_prefix_sum_gives_placement_offsets() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "count", &[2, 1, 2]);

    // Prefix defined via expressions from count (not concrete values)
    assume_seq_i64_exprs(
        &mut ctx,
        "prefix",
        &[
            "0",                               // prefix[0] = 0
            "count.index(0)",                  // prefix[1] = count[0]
            "count.index(0) + count.index(1)", // prefix[2] = count[0] + count[1]
        ],
    );

    // Derived: last offset + last count == total source length
    ctx.push_assert(
        "total_conservation",
        "prefix.index(2) + count.index(2) == count.index(0) + count.index(1) + count.index(2)",
    );
    // Prefix is monotonically non-decreasing
    ctx.push_assert("monotone_01", "prefix.index(0) <= prefix.index(1)");
    ctx.push_assert("monotone_12", "prefix.index(1) <= prefix.index(2)");
    // Prefix differences match counts
    ctx.push_assert(
        "diff_01_matches_count0",
        "prefix.index(1) - prefix.index(0) == count.index(0)",
    );
    ctx.push_assert(
        "diff_12_matches_count1",
        "prefix.index(2) - prefix.index(1) == count.index(1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 39b: prefix sum offsets should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Output correctness
// ========================================================================

/// Tier 39c: Placement phase produces sorted output.
///
/// src = [2, 0, 2, 1, 0] -> output = [0, 0, 1, 2, 2].
/// Cross-state assertion: sum(out) == sum(src) (permutation sum invariant).
#[test]
fn test_vt_tier39c_placement_produces_sorted_output() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "src", &[2, 0, 2, 1, 0]);
    assume_seq_i64(&mut ctx, "out", &[0, 0, 1, 2, 2]);

    // Sorted property: out[i] <= out[i+1]
    ctx.push_assert("sorted01", "out.index(0) <= out.index(1)");
    ctx.push_assert("sorted12", "out.index(1) <= out.index(2)");
    ctx.push_assert("sorted23", "out.index(2) <= out.index(3)");
    ctx.push_assert("sorted34", "out.index(3) <= out.index(4)");
    // Cross-state sum conservation: sum(out) == sum(src)
    ctx.push_assert(
        "sum_conservation",
        "out.index(0) + out.index(1) + out.index(2) + out.index(3) + out.index(4) == src.index(0) + src.index(1) + src.index(2) + src.index(3) + src.index(4)",
    );
    // Size preserved
    ctx.push_assert("size_preserved", "out.len() == src.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 39c: sorted output should verify, got: {:?}",
        result,
    );
}

/// Tier 39d: Output preserves element counts (permutation property).
///
/// The frequency of each value is derived from the concrete `src` and `out`
/// sequences via indicator sums rather than separate assumed count arrays.
#[test]
fn test_vt_tier39d_output_preserves_element_counts() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "src", &[2, 0, 2, 1, 0]);
    assume_seq_i64(&mut ctx, "out", &[0, 0, 1, 2, 2]);
    let src_zeros = occurrence_sum_expr("src", 0, 5);
    let src_ones = occurrence_sum_expr("src", 1, 5);
    let src_twos = occurrence_sum_expr("src", 2, 5);
    let out_zeros = occurrence_sum_expr("out", 0, 5);
    let out_ones = occurrence_sum_expr("out", 1, 5);
    let out_twos = occurrence_sum_expr("out", 2, 5);

    // Permutation: same counts for each value
    ctx.push_assert("perm0", &format!("{src_zeros} == {out_zeros}"));
    ctx.push_assert("perm1", &format!("{src_ones} == {out_ones}"));
    ctx.push_assert("perm2", &format!("{src_twos} == {out_twos}"));
    // Derived counts cover the entire sequence on both sides
    ctx.push_assert(
        "total_src",
        &format!("{src_zeros} + {src_ones} + {src_twos} == src.len()"),
    );
    ctx.push_assert(
        "total_out",
        &format!("{out_zeros} + {out_ones} + {out_twos} == out.len()"),
    );
    // Weighted-sum equality across the derived src/out multiplicities
    ctx.push_assert(
        "weighted_sum_equal",
        &format!("{src_ones} + {src_twos} + {src_twos} == {out_ones} + {out_twos} + {out_twos}"),
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 39d: permutation property should verify, got: {:?}",
        result,
    );
}

/// Tier 39e: Concrete end-to-end counting sort trace.
///
/// Traces through count, prefix-sum, and placement for src = [1, 0, 2, 0].
/// Prefix defined via expressions from count. Cross-phase conservation.
#[test]
fn test_vt_tier39e_end_to_end_counting_sort_trace() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "src", &[1, 0, 2, 0]);
    assume_seq_i64(&mut ctx, "count", &[2, 1, 1]);
    assume_seq_i64(&mut ctx, "out", &[0, 0, 1, 2]);

    // Prefix defined via expressions from count
    assume_seq_i64_exprs(
        &mut ctx,
        "prefix",
        &["0", "count.index(0)", "count.index(0) + count.index(1)"],
    );

    // Sorted output
    ctx.push_assert("sorted01", "out.index(0) <= out.index(1)");
    ctx.push_assert("sorted12", "out.index(1) <= out.index(2)");
    ctx.push_assert("sorted23", "out.index(2) <= out.index(3)");
    // Last prefix + last count == source length (chain through expressions)
    ctx.push_assert(
        "prefix_count_total",
        "prefix.index(2) + count.index(2) == src.len()",
    );
    // Sum conservation: sum(out) == sum(src)
    ctx.push_assert(
        "sum_conservation",
        "out.index(0) + out.index(1) + out.index(2) + out.index(3) == src.index(0) + src.index(1) + src.index(2) + src.index(3)",
    );
    // Weighted-sum conservation: Σ v*count[v] == sum(src)
    ctx.push_assert(
        "weighted_sum_conservation",
        "count.index(1) + count.index(2) + count.index(2) == src.index(0) + src.index(1) + src.index(2) + src.index(3)",
    );
    // Count total
    ctx.push_assert(
        "count_total",
        "count.index(0) + count.index(1) + count.index(2) == src.len()",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 39e: end-to-end counting sort should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Soundness negatives
// ========================================================================

/// Tier 39f: Wrong count rejects permutation claim.
///
/// If count[0] is off by 1, the direct permutation equality claim should fail.
#[test]
fn test_vt_tier39f_wrong_count_rejects_permutation() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "count_src", &[2, 1, 2]);
    // WRONG output counts: count_out[0] = 1 instead of 2 (lost an element)
    assume_seq_i64(&mut ctx, "count_out", &[1, 1, 2]);

    // Claim same counts — should be rejected
    ctx.push_assert("perm0", "count_src.index(0) == count_out.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 39f SOUNDNESS: wrong count should be rejected, got: {:?}",
        result,
    );
}

/// Tier 39g: Skipping prefix-sum produces wrong placement.
///
/// Without prefix offsets, placing all 0s at index 0 and all 1s at index 1
/// overwrites rather than appending. The output no longer preserves the
/// source sum.
#[test]
fn test_vt_tier39g_wrong_placement_breaks_conservation() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "src", &[1, 0, 2, 0]);
    assume_seq_i64(&mut ctx, "out", &[0, 1, 2, 99]);

    // WRONG: total doesn't match because of overwritten garbage value
    ctx.push_assert(
        "wrong_sum",
        "out.index(0) + out.index(1) + out.index(2) + out.index(3) == src.index(0) + src.index(1) + src.index(2) + src.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 39g SOUNDNESS: wrong placement sum should be rejected, got: {:?}",
        result,
    );
}

/// Tier 39h: Off-by-one in prefix sum shifts entire output.
///
/// prefix = [1, 3, 4] instead of [0, 2, 3] — all placements shift right.
/// The prefix-count total no longer equals the source length.
#[test]
fn test_vt_tier39h_off_by_one_prefix_breaks_total() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "count", &[2, 1, 2]);

    // WRONG prefix: starts at 1 instead of 0, defined via expressions
    assume_seq_i64_exprs(
        &mut ctx,
        "prefix",
        &[
            "1",                                   // WRONG: should be 0
            "1 + count.index(0)",                  // 1+2=3
            "1 + count.index(0) + count.index(1)", // 1+2+1=4
        ],
    );

    // Claim last_offset + last_count == total_elements (should fail: 4+2=6≠5)
    ctx.push_assert(
        "total_correct",
        "prefix.index(2) + count.index(2) == count.index(0) + count.index(1) + count.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 39h SOUNDNESS: off-by-one prefix should be rejected, got: {:?}",
        result,
    );
}
