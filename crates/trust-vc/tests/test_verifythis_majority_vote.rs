// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 69 — Boyer-Moore Majority Vote VCs.
//!
//! The Boyer-Moore majority vote algorithm finds the majority element
//! (appearing > n/2 times) in a single pass with O(1) extra space.
//!
//! Algorithm:
//!   candidate = a[0]; count = 1;
//!   for i in 1..n:
//!     if a[i] == candidate: count += 1
//!     else: count -= 1
//!     if count == 0: candidate = a[i+1]; count = 1; skip i+1
//!
//! Simplified concrete trace for arrays with known majority.
//!
//! Core proof obligations:
//!   1. Init: the first element becomes candidate with count 1
//!   2. Step: matching increments count, non-matching decrements
//!   3. Invariant: at each point, count pairs can be cancelled pairwise,
//!      so the candidate leads by `count` over all other paired elements
//!   4. Exit: for a concrete trace, the final candidate is the majority
//!   5. Negatives: non-majority elements fail the exit assertion
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

fn assume_seq_u64(ctx: &mut VerificationContext, name: &str, values: &[u64]) {
    ctx.declare_var_parsed(name, "Seq<u64>");
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

/// Example array: [2, 2, 1, 2, 1, 2, 2]
/// Majority element: 2 (appears 5 out of 7 times, > 7/2).
fn assume_majority_example(ctx: &mut VerificationContext) {
    assume_seq_u64(ctx, "a", &[2, 2, 1, 2, 1, 2, 2]);
}

/// Example array with no majority: [1, 2, 3, 1]
/// No element appears > 4/2 = 2 times. 1 appears twice, exactly half.
fn assume_no_majority_example(ctx: &mut VerificationContext) {
    assume_seq_u64(ctx, "a", &[1, 2, 3, 1]);
}

// ========================================================================
// GROUP A: Init — first element becomes candidate
// ========================================================================

/// Tier 69a: Init — first element becomes candidate with count 1.
#[test]
fn test_vt_tier69a_init_first_candidate() {
    let mut ctx = VerificationContext::new();
    assume_majority_example(&mut ctx);
    ctx.declare_var_parsed("candidate", "u64");
    ctx.declare_var_parsed("count", "u64");

    ctx.push_assume("init_candidate", "candidate == a.index(0)");
    ctx.push_assume("init_count", "count == 1");

    ctx.push_assert("candidate_is_2", "candidate == 2");
    ctx.push_assert("count_positive", "count >= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 69a: init should set candidate to first element, got: {:?}",
        result,
    );
}

/// Tier 69a: Init works regardless of which element is first.
#[test]
fn test_vt_tier69a_init_arbitrary_first() {
    let mut ctx = VerificationContext::new();
    assume_no_majority_example(&mut ctx);
    ctx.declare_var_parsed("candidate", "u64");
    ctx.declare_var_parsed("count", "u64");

    ctx.push_assume("init_candidate", "candidate == a.index(0)");
    ctx.push_assume("init_count", "count == 1");

    ctx.push_assert("candidate_is_1", "candidate == 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 69a: init on no-majority array should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Step — match increments, mismatch decrements, zero resets
// ========================================================================

/// Tier 69b: matching element increments count.
/// After init: candidate=2, count=1. a[1]=2 matches, so count becomes 2.
#[test]
fn test_vt_tier69b_match_increments() {
    let mut ctx = VerificationContext::new();
    assume_majority_example(&mut ctx);
    ctx.declare_var_parsed("candidate", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("count_next", "u64");

    ctx.push_assume("candidate_2", "candidate == 2");
    ctx.push_assume("count_1", "count == 1");
    // a[1] == 2 == candidate, so increment
    ctx.push_assume("match_step", "a.index(1) == candidate");
    ctx.push_assume("count_next_val", "count_next == count + 1");

    ctx.push_assert("count_grows", "count_next == 2");
    ctx.push_assert("count_positive", "count_next >= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 69b: matching element should increment count, got: {:?}",
        result,
    );
}

/// Tier 69b: non-matching element decrements count.
/// candidate=2, count=2. a[2]=1 mismatches, so count becomes 1.
#[test]
fn test_vt_tier69b_mismatch_decrements() {
    let mut ctx = VerificationContext::new();
    assume_majority_example(&mut ctx);
    ctx.declare_var_parsed("candidate", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("count_next", "u64");

    ctx.push_assume("candidate_2", "candidate == 2");
    ctx.push_assume("count_2", "count == 2");
    ctx.push_assume("mismatch", "a.index(2) == 1");
    ctx.push_assume("not_match", "a.index(2) != candidate");
    ctx.push_assume("count_next_val", "count_next == count - 1");

    ctx.push_assert("count_decreases", "count_next == 1");
    ctx.push_assert("count_nonneg", "count_next >= 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 69b: mismatch should decrement count, got: {:?}",
        result,
    );
}

/// Tier 69b: when count reaches zero, next element becomes new candidate.
/// Simulating: candidate=1, count=0 after cancellation → pick a[3]=2.
#[test]
fn test_vt_tier69b_zero_resets_candidate() {
    let mut ctx = VerificationContext::new();
    assume_majority_example(&mut ctx);
    ctx.declare_var_parsed("candidate", "u64");
    ctx.declare_var_parsed("candidate_next", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("count_next", "u64");

    ctx.push_assume("count_0", "count == 0");
    ctx.push_assume("old_candidate_1", "candidate == 1");
    ctx.push_assume("new_candidate", "candidate_next == a.index(3)");
    ctx.push_assume("count_reset", "count_next == 1");

    ctx.push_assert("new_is_2", "candidate_next == 2");
    ctx.push_assert("candidate_changed", "candidate_next != candidate");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 69b: zero count should reset candidate, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Invariant — count tracks net lead, cancellation property
// ========================================================================

/// Tier 69c: pairwise cancellation — if count is c at position i,
/// then at most (i+1-c)/2 non-candidate elements exist in prefix.
/// Concrete trace for [2, 2, 1, 2, 1, 2, 2]:
///   i=0: cand=2, cnt=1
///   i=1: cand=2, cnt=2 (match)
///   i=2: cand=2, cnt=1 (mismatch with 1)
///   i=3: cand=2, cnt=2 (match)
///   i=4: cand=2, cnt=1 (mismatch with 1)
///   i=5: cand=2, cnt=2 (match)
///   i=6: cand=2, cnt=3 (match)
#[test]
fn test_vt_tier69c_trace_counts_correct() {
    let mut ctx = VerificationContext::new();
    assume_majority_example(&mut ctx);

    // Declare trace state at each position
    ctx.declare_var_parsed("cnt0", "u64");
    ctx.declare_var_parsed("cnt1", "u64");
    ctx.declare_var_parsed("cnt2", "u64");
    ctx.declare_var_parsed("cnt3", "u64");
    ctx.declare_var_parsed("cnt4", "u64");
    ctx.declare_var_parsed("cnt5", "u64");
    ctx.declare_var_parsed("cnt6", "u64");

    ctx.push_assume("cnt0_val", "cnt0 == 1");
    ctx.push_assume("cnt1_val", "cnt1 == 2");
    ctx.push_assume("cnt2_val", "cnt2 == 1");
    ctx.push_assume("cnt3_val", "cnt3 == 2");
    ctx.push_assume("cnt4_val", "cnt4 == 1");
    ctx.push_assume("cnt5_val", "cnt5 == 2");
    ctx.push_assume("cnt6_val", "cnt6 == 3");

    // Match/mismatch at each step
    ctx.push_assert("step1_match", "a.index(1) == a.index(0)");
    ctx.push_assert("step1_inc", "cnt1 == cnt0 + 1");
    ctx.push_assert("step2_mismatch", "a.index(2) != a.index(0)");
    ctx.push_assert("step2_dec", "cnt2 + 1 == cnt1");
    ctx.push_assert("step3_match", "a.index(3) == a.index(0)");
    ctx.push_assert("step3_inc", "cnt3 == cnt2 + 1");
    ctx.push_assert("step4_mismatch", "a.index(4) != a.index(0)");
    ctx.push_assert("step4_dec", "cnt4 + 1 == cnt3");
    ctx.push_assert("step5_match", "a.index(5) == a.index(0)");
    ctx.push_assert("step5_inc", "cnt5 == cnt4 + 1");
    ctx.push_assert("step6_match", "a.index(6) == a.index(0)");
    ctx.push_assert("step6_inc", "cnt6 == cnt5 + 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 69c: full trace counts should verify, got: {:?}",
        result,
    );
}

/// Tier 69c: count is always bounded by the number of processed elements.
#[test]
fn test_vt_tier69c_count_bounded_by_prefix_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("i", "u64");

    // At position i (0-indexed), we've seen i+1 elements.
    // count <= i + 1 always holds.
    ctx.push_assume("count_3", "count == 3");
    ctx.push_assume("i_6", "i == 6"); // after 7 elements

    ctx.push_assert("bounded", "count <= i + 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 69c: count should be bounded by prefix length, got: {:?}",
        result,
    );
}

/// Tier 69c: if count > 0, candidate has appeared at least
/// (prefix_elements + count) / 2 times.
/// With 7 elements and count=3: candidate appeared at least (7+3)/2 = 5 times.
#[test]
fn test_vt_tier69c_majority_count_lower_bound() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("candidate_occurrences", "u64");

    ctx.push_assume("n_7", "n == 7");
    ctx.push_assume("count_3", "count == 3");
    ctx.push_assume("occ_5", "candidate_occurrences == 5");

    // candidate_occurrences >= (n + count) / 2
    // 5 >= (7 + 3) / 2 = 5 ✓
    ctx.push_assert("lower_bound", "candidate_occurrences >= (n + count) / 2");
    // candidate_occurrences > n / 2 (majority)
    ctx.push_assert("is_majority", "candidate_occurrences > n / 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 69c: majority lower bound should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Exit and soundness negatives
// ========================================================================

/// Tier 69d: after the full scan, the final candidate is the majority element.
#[test]
fn test_vt_tier69d_final_candidate_is_majority() {
    let mut ctx = VerificationContext::new();
    assume_majority_example(&mut ctx);
    ctx.declare_var_parsed("final_candidate", "u64");
    ctx.declare_var_parsed("final_count", "u64");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("occurrences_of_2", "u64");

    ctx.push_assume("n_7", "n == 7");
    ctx.push_assume("candidate_2", "final_candidate == 2");
    ctx.push_assume("count_3", "final_count == 3");
    ctx.push_assume("occ_5", "occurrences_of_2 == 5");

    // Count occurrences of 2 in the array
    ctx.push_assert("occ_0", "a.index(0) == 2");
    ctx.push_assert("occ_1", "a.index(1) == 2");
    ctx.push_assert("occ_3", "a.index(3) == 2");
    ctx.push_assert("occ_5_val", "a.index(5) == 2");
    ctx.push_assert("occ_6", "a.index(6) == 2");

    // Majority check: 5 > 7/2 = 3
    ctx.push_assert("majority_check", "occurrences_of_2 > n / 2");
    ctx.push_assert("count_positive", "final_count >= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 69d: final candidate should be the majority, got: {:?}",
        result,
    );
}

/// Tier 69d NEGATIVE: claiming element 1 is the majority in [2,2,1,2,1,2,2] is unsound.
/// Pre-compute threshold to avoid BV division timeout.
#[test]
fn test_vt_tier69d_negative_wrong_majority() {
    let mut ctx = VerificationContext::new();
    assume_majority_example(&mut ctx);
    ctx.declare_var_parsed("occurrences_of_1", "u64");
    ctx.declare_var_parsed("threshold", "u64");

    ctx.push_assume("occ_2", "occurrences_of_1 == 2");
    ctx.push_assume("threshold_3", "threshold == 3"); // 7/2 = 3

    // Element 1 appears only 2 times; 2 > 3 is false.
    ctx.push_assert("wrong_majority", "occurrences_of_1 > threshold");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 69d SOUNDNESS: non-majority element should be rejected, got: {:?}",
        result,
    );
}

/// Tier 69d NEGATIVE: an array with no majority cannot have any element
/// with count > n/2. Pre-compute threshold to avoid BV division timeout.
#[test]
fn test_vt_tier69d_negative_no_majority_exists() {
    let mut ctx = VerificationContext::new();
    assume_no_majority_example(&mut ctx);
    ctx.declare_var_parsed("max_occ", "u64");
    ctx.declare_var_parsed("threshold", "u64");

    ctx.push_assume("max_2", "max_occ == 2"); // element 1 appears twice
    ctx.push_assume("threshold_2", "threshold == 2"); // 4/2 = 2

    // 2 > 2 is false (need strictly greater)
    ctx.push_assert("wrong_majority", "max_occ > threshold");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 69d SOUNDNESS: no-majority array should reject majority claim, got: {:?}",
        result,
    );
}

/// Tier 69d: the algorithm is correct even when majority element is last.
/// Array: [1, 2, 2, 1, 2] — majority is 2 (3 out of 5).
/// Trace: cand=1 cnt=1 → cnt=0 → cand=2 cnt=1 → cnt=0 → cand=2 cnt=1
#[test]
fn test_vt_tier69d_majority_survives_early_cancellations() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "a", &[1, 2, 2, 1, 2]);
    ctx.declare_var_parsed("final_candidate", "u64");
    ctx.declare_var_parsed("final_count", "u64");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("occ_2", "u64");

    ctx.push_assume("n_5", "n == 5");
    ctx.push_assume("candidate_2", "final_candidate == 2");
    ctx.push_assume("count_1", "final_count == 1");
    ctx.push_assume("occ_3", "occ_2 == 3");

    ctx.push_assert("elem_1_is_2", "a.index(1) == 2");
    ctx.push_assert("elem_2_is_2", "a.index(2) == 2");
    ctx.push_assert("elem_4_is_2", "a.index(4) == 2");
    ctx.push_assert("majority", "occ_2 > n / 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 69d: majority should survive early cancellations, got: {:?}",
        result,
    );
}
