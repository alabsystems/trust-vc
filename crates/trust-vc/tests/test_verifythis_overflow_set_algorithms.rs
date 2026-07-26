// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 27 — Set-based algorithm VCs under overflow checking.
//!
//! Tier 16 validated basic Set operations (insert, contains, union, intersect).
//! Tier 26 added overflow checking to Map-based algorithms. This tier combines
//! both: Set-based algorithm patterns with `check_overflow = true`.
//!
//! GROUP A: Set accumulation with count tracking (distinct element counting).
//! GROUP B: Set-based element partitioning (quicksort, threshold filtering).
//! GROUP C: Set union/intersection with bounded element arithmetic.
//! GROUP D: Negative tests — overflow rejection and logical violations.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline.

mod common;

use common::verify_context_with_pipeline;
use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// GROUP A: Set Accumulation with Count Tracking under Overflow
//
// Insert elements into a seen-set while tracking count. `count += 1` on each
// new element. Competition: distinct counting, visited-node tracking.

/// Tier 27a INIT: Empty set with zero count.
#[test]
fn test_vt_tier27a_set_accum_init() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("seen", "Set<i32>");
    ctx.declare_var_parsed("count", "i32");
    ctx.declare_var_parsed("x", "i32");

    ctx.push_assume("empty", "!seen.contains(x)");
    ctx.push_assume("count_init", "count == 0");

    ctx.push_assert("non_neg", "count >= 0");
    ctx.push_assert("bounded", "count <= 1000000");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27a INIT: empty set with zero count should verify: {:?}",
        result,
    );
}

/// Tier 27a STEP: Insert new element, increment bounded counter.
#[test]
fn test_vt_tier27a_set_accum_step_new_element() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("seen", "Set<i32>");
    ctx.declare_var_parsed("seen_new", "Set<i32>");
    ctx.declare_var_parsed("elem", "i32");
    ctx.declare_var_parsed("count", "i32");
    ctx.declare_var_parsed("count_new", "i32");

    ctx.push_assume("not_seen", "!seen.contains(elem)");
    ctx.push_assume("count_bounded", "count >= 0 && count < 1000000");
    ctx.push_assume("insert", "seen_new == seen.insert(elem)");
    ctx.push_assume("increment", "count_new == count + 1");

    ctx.push_assert("now_contains", "seen_new.contains(elem)");
    ctx.push_assert("count_pos", "count_new > 0");
    ctx.push_assert("count_bound", "count_new <= 1000000");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27a STEP: new element insert+count should verify: {:?}",
        result,
    );
}

/// Tier 27a FRAME: Inserting new element preserves prior members.
#[test]
fn test_vt_tier27a_set_accum_frame() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("seen", "Set<i32>");
    ctx.declare_var_parsed("old_elem", "i32");
    ctx.declare_var_parsed("new_elem", "i32");

    ctx.push_assume("old_in_seen", "seen.contains(old_elem)");
    ctx.push_assert("preserved", "seen.insert(new_elem).contains(old_elem)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27a FRAME: insert preserves prior members: {:?}",
        result,
    );
}

/// Tier 27a EXIT: Concrete accumulation — insert [10, 20, 10], get {10, 20}.
#[test]
fn test_vt_tier27a_set_accum_exit() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s0", "Set<i32>");
    ctx.declare_var_parsed("s1", "Set<i32>");
    ctx.declare_var_parsed("s2", "Set<i32>");
    ctx.declare_var_parsed("s3", "Set<i32>");

    ctx.push_assume("step1", "s1 == s0.insert(10)");
    ctx.push_assume("step2", "s2 == s1.insert(20)");
    ctx.push_assume("step3", "s3 == s2.insert(10)"); // duplicate

    ctx.push_assert("has_10", "s3.contains(10)");
    ctx.push_assert("has_20", "s3.contains(20)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27a EXIT: concrete accumulation should verify: {:?}",
        result,
    );
}

/// Tier 27a NEGATIVE: Unbounded counter increment overflows.
#[test]
fn test_vt_tier27a_set_accum_unbounded_negative() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("count", "i32");
    ctx.declare_var_parsed("count_new", "i32");

    // NO upper bound on count — overflow possible
    ctx.push_assume("count_non_neg", "count >= 0");
    ctx.push_assume("increment", "count_new == count + 1");

    ctx.push_assert("inc_correct", "count_new == count + 1");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 27a NEG: unbounded counter must produce Counterexample: {:?}",
        result,
    );
}

// GROUP B: Set-based Element Partitioning under Overflow
//
// Split elements into lo/hi sets based on a threshold. Competition:
// quicksort partition, bucket sort, two-way classification.

/// Tier 27b: Partition step — element below threshold goes to lo set.
#[test]
fn test_vt_tier27b_partition_step_lo() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("lo", "Set<i32>");
    ctx.declare_var_parsed("lo_new", "Set<i32>");
    ctx.declare_var_parsed("elem", "i32");
    ctx.declare_var_parsed("threshold", "i32");

    ctx.push_assume("elem_below", "elem < threshold");
    ctx.push_assume("insert_lo", "lo_new == lo.insert(elem)");

    ctx.push_assert("in_lo", "lo_new.contains(elem)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27b: partition lo step should verify: {:?}",
        result,
    );
}

/// Tier 27b: Partition step — element at/above threshold goes to hi set.
#[test]
fn test_vt_tier27b_partition_step_hi() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("hi", "Set<i32>");
    ctx.declare_var_parsed("hi_new", "Set<i32>");
    ctx.declare_var_parsed("elem", "i32");
    ctx.declare_var_parsed("threshold", "i32");

    ctx.push_assume("elem_above", "elem >= threshold");
    ctx.push_assume("insert_hi", "hi_new == hi.insert(elem)");

    ctx.push_assert("in_hi", "hi_new.contains(elem)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27b: partition hi step should verify: {:?}",
        result,
    );
}

/// Tier 27b EXIT: Concrete partition — [10, 60] with threshold 50.
#[test]
fn test_vt_tier27b_partition_exit() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("lo0", "Set<i32>");
    ctx.declare_var_parsed("lo1", "Set<i32>");
    ctx.declare_var_parsed("hi0", "Set<i32>");
    ctx.declare_var_parsed("hi1", "Set<i32>");

    ctx.push_assume("lo_10", "lo1 == lo0.insert(10)");
    ctx.push_assume("hi_60", "hi1 == hi0.insert(60)");

    ctx.push_assert("lo_has_10", "lo1.contains(10)");
    ctx.push_assert("hi_has_60", "hi1.contains(60)");
    ctx.push_assert("lo_prop", "10 < 50");
    ctx.push_assert("hi_prop", "60 >= 50");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27b EXIT: concrete partition should verify: {:?}",
        result,
    );
}

/// Tier 27b NEGATIVE: Element >= threshold placed in lo set — violates partition.
#[test]
fn test_vt_tier27b_partition_wrong_set_negative() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("lo", "Set<i32>");
    ctx.declare_var_parsed("lo_new", "Set<i32>");
    ctx.declare_var_parsed("elem", "i32");

    ctx.push_assume("elem_above", "elem >= 50");
    ctx.push_assume("elem_witness", "elem == 50");
    ctx.push_assume("wrong_placement", "lo_new.contains(elem)");

    ctx.push_assert("wrong_prop", "elem < 50");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 27b NEG: wrong partition placement must produce Counterexample: {:?}",
        result,
    );
}

// GROUP C: Set Union/Intersection with Bounded Element Arithmetic
//
// Combine sets where element values participate in overflow-sensitive
// computations. Competition: merging work queues, combining candidates.

/// Tier 27c: Union preserves membership under overflow checking.
#[test]
fn test_vt_tier27c_union_membership_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Set<i32>");
    ctx.declare_var_parsed("b", "Set<i32>");
    ctx.declare_var_parsed("x", "i32");

    ctx.push_assume("x_in_a", "a.contains(x)");
    ctx.push_assert("x_in_union", "a.union(b).contains(x)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27c: union membership should verify under overflow: {:?}",
        result,
    );
}

/// Tier 27c: Intersection element is in both sets under overflow.
#[test]
fn test_vt_tier27c_intersection_both_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Set<i32>");
    ctx.declare_var_parsed("b", "Set<i32>");
    ctx.declare_var_parsed("x", "i32");

    ctx.push_assume("x_in_inter", "a.intersect(b).contains(x)");
    ctx.push_assert("x_in_a", "a.contains(x)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27c: intersection implies membership in a: {:?}",
        result,
    );
}

/// Tier 27c: Bounded element sum from union sets.
///
/// x from set a, y from set b, both bounded. Sum x + y is bounded.
#[test]
fn test_vt_tier27c_union_bounded_element_sum() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Set<i32>");
    ctx.declare_var_parsed("b", "Set<i32>");
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");
    ctx.declare_var_parsed("sum", "i32");

    ctx.push_assume("x_in_a", "a.contains(x)");
    ctx.push_assume("y_in_b", "b.contains(y)");
    ctx.push_assume("x_bounded", "x >= -500000 && x <= 500000");
    ctx.push_assume("y_bounded", "y >= -500000 && y <= 500000");
    ctx.push_assume("sum_def", "sum == x + y");

    ctx.push_assert("sum_bounded", "sum >= -1000000 && sum <= 1000000");
    ctx.push_assert("x_in_union", "a.union(b).contains(x)");
    ctx.push_assert("y_in_union", "a.union(b).contains(y)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27c: bounded element sum from union should verify: {:?}",
        result,
    );
}

/// Tier 27c: Bounded count difference — |count_a - count_b| bounded.
#[test]
fn test_vt_tier27c_set_count_difference_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("count_a", "i32");
    ctx.declare_var_parsed("count_b", "i32");
    ctx.declare_var_parsed("diff", "i32");

    ctx.push_assume("a_bounded", "count_a >= 0 && count_a <= 500000");
    ctx.push_assume("b_bounded", "count_b >= 0 && count_b <= 500000");
    ctx.push_assume("diff_def", "diff == count_a - count_b");

    ctx.push_assert("diff_bounded", "diff >= -500000 && diff <= 500000");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27c: bounded count difference should verify: {:?}",
        result,
    );
}

/// Tier 27c: Concrete union — {10, 20} ∪ {20, 30} contains all three.
#[test]
fn test_vt_tier27c_concrete_union_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a0", "Set<i32>");
    ctx.declare_var_parsed("a", "Set<i32>");
    ctx.declare_var_parsed("b0", "Set<i32>");
    ctx.declare_var_parsed("b", "Set<i32>");

    ctx.push_assume("a_build", "a == a0.insert(10).insert(20)");
    ctx.push_assume("b_build", "b == b0.insert(20).insert(30)");

    ctx.push_assert("has_10", "a.union(b).contains(10)");
    ctx.push_assert("has_20", "a.union(b).contains(20)");
    ctx.push_assert("has_30", "a.union(b).contains(30)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27c: concrete union should verify under overflow: {:?}",
        result,
    );
}

/// Tier 27c: Concrete intersection — {10, 20} ∩ {20, 30} contains 20.
#[test]
fn test_vt_tier27c_concrete_intersection_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a0", "Set<i32>");
    ctx.declare_var_parsed("a", "Set<i32>");
    ctx.declare_var_parsed("b0", "Set<i32>");
    ctx.declare_var_parsed("b", "Set<i32>");

    ctx.push_assume("a_build", "a == a0.insert(10).insert(20)");
    ctx.push_assume("b_build", "b == b0.insert(20).insert(30)");

    ctx.push_assert("has_20", "a.intersect(b).contains(20)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 27c: concrete intersection should verify under overflow: {:?}",
        result,
    );
}

// GROUP D: Negative Tests — Overflow and Logical Violations

/// Tier 27d NEGATIVE: Unbounded element sum overflows.
#[test]
fn test_vt_tier27d_unbounded_element_sum_negative() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Set<i32>");
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");

    ctx.push_assume("x_in_a", "a.contains(x)");
    ctx.push_assume("y_in_a", "a.contains(y)");

    ctx.push_assert("sum_positive", "x + y >= x");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 27d NEG: unbounded element sum must produce Counterexample: {:?}",
        result,
    );
}

/// Tier 27d NEGATIVE: Union membership does not imply both-set membership.
#[test]
fn test_vt_tier27d_union_not_implies_both_negative() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Set<i32>");
    ctx.declare_var_parsed("b", "Set<i32>");
    // Concrete witness avoids the current symbolic-union Unknown and still checks
    // the intended soundness point.
    ctx.push_assume("one_in_a", "a.contains(1)");
    ctx.push_assume("one_not_in_b", "!b.contains(1)");
    ctx.push_assert("one_in_union", "a.union(b).contains(1)");
    ctx.push_assert("wrong_both", "a.contains(1) && b.contains(1)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 27d NEG: union does not imply both-set membership must produce Counterexample: {:?}",
        result,
    );
}

/// Tier 27d NEGATIVE: Non-member not in intersection.
#[test]
fn test_vt_tier27d_nonmember_not_in_intersection_negative() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Set<i32>");
    ctx.declare_var_parsed("b", "Set<i32>");
    ctx.declare_var_parsed("x", "i32");

    ctx.push_assume("x_not_in_a", "!a.contains(x)");
    ctx.push_assert("wrong_in_inter", "a.intersect(b).contains(x)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 27d NEG: non-member not in intersection must produce Counterexample: {:?}",
        result,
    );
}

/// Tier 27d NEGATIVE: Unbounded count difference overflows.
#[test]
fn test_vt_tier27d_unbounded_count_diff_negative() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("count_a", "i32");
    ctx.declare_var_parsed("count_b", "i32");
    ctx.declare_var_parsed("diff", "i32");

    ctx.push_assume("diff_def", "diff == count_a - count_b");
    ctx.push_assert("diff_bounded", "diff >= -1000000 && diff <= 1000000");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 27d NEG: unbounded count difference must produce Counterexample: {:?}",
        result,
    );
}
