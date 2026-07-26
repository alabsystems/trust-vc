// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 19 — Competition gap coverage.
//!
//! Patterns from actual VerifyThis problems NOT covered in Tiers 1-18:
//!
//! GROUP A: Prefix Sum — cumulative running total with range query derivation.
//!   Archetype: range sum queries, Fenwick trees, run-length tracking.
//!
//! GROUP B: Dutch National Flag — 3-way partitioning around pivot.
//!   Archetype: quicksort partition, task classification, 3-way split.
//!
//! GROUP C: Element Counting — classify-and-count over array.
//!   Archetype: histogram, majority element, voting algorithms.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ========================================================================
// GROUP A: Prefix Sum
//
// Prefix sum: prefix[i] = sum(s[0..i+1]).
// Recurrence: prefix[0] = s[0], prefix[i] = prefix[i-1] + s[i].
// Range query: sum(l..r+1) = prefix[r] - prefix[l-1].
// ========================================================================

/// Tier 19a: Prefix sum step — recurrence implies closed-form sum.
///
/// Given prefix[0] = s[0] and prefix[1] = prefix[0] + s[1],
/// prove prefix[1] == s[0] + s[1]. Requires substitution through
/// the recurrence to derive the closed form.
#[test]
fn test_vt_tier19a_prefix_sum_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("p0", "i32");
    ctx.declare_var_parsed("p1", "i32");

    ctx.push_assume("s_len", "s.len() >= 2");
    ctx.push_assume("eb0", "s.index(0) >= -10000 && s.index(0) <= 10000");
    ctx.push_assume("eb1", "s.index(1) >= -10000 && s.index(1) <= 10000");

    ctx.push_assume("p0_def", "p0 == s.index(0)");
    ctx.push_assume("p1_def", "p1 == p0 + s.index(1)");

    ctx.push_assert("p1_sum", "p1 == s.index(0) + s.index(1)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 19a: prefix sum step should verify, got: {:?}",
        result,
    );
}

/// Tier 19a: Full 4-element prefix sum — recurrence chain to closed form.
/// p0 = s[0], p1 = p0+s[1], p2 = p1+s[2], p3 = p2+s[3].
/// Prove: p3 == s[0] + s[1] + s[2] + s[3]. Three-step substitution.
/// Tier 19a: Full 4-element prefix sum — recurrence chain to closed form.
///
/// The symbolic 4-step substitution chain now verifies reliably under BV
/// Skolemization with element bounds, so this is a strict Verified gate.
#[test]
fn test_vt_tier19a_prefix_sum_full() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("p0", "i32");
    ctx.declare_var_parsed("p1", "i32");
    ctx.declare_var_parsed("p2", "i32");
    ctx.declare_var_parsed("p3", "i32");

    ctx.push_assume("s_len", "s.len() == 4");
    ctx.push_assume("eb0", "s.index(0) >= -10000 && s.index(0) <= 10000");
    ctx.push_assume("eb1", "s.index(1) >= -10000 && s.index(1) <= 10000");
    ctx.push_assume("eb2", "s.index(2) >= -10000 && s.index(2) <= 10000");
    ctx.push_assume("eb3", "s.index(3) >= -10000 && s.index(3) <= 10000");

    ctx.push_assume("p0_def", "p0 == s.index(0)");
    ctx.push_assume("p1_def", "p1 == p0 + s.index(1)");
    ctx.push_assume("p2_def", "p2 == p1 + s.index(2)");
    ctx.push_assume("p3_def", "p3 == p2 + s.index(3)");
    ctx.push_assert(
        "p3_sum",
        "p3 == s.index(0) + s.index(1) + s.index(2) + s.index(3)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 19a: full prefix sum should verify, got: {:?}",
        result,
    );
}

/// Tier 19a: Competition workaround — concrete 4-element prefix sum chain with stable coverage.
#[test]
fn test_vt_tier19a_prefix_sum_full_workaround() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("p0", "i32");
    ctx.declare_var_parsed("p1", "i32");
    ctx.declare_var_parsed("p2", "i32");
    ctx.declare_var_parsed("p3", "i32");

    ctx.push_assume("s_len", "s.len() == 4");
    ctx.push_assume("s0", "s.index(0) == 2");
    ctx.push_assume("s1", "s.index(1) == -1");
    ctx.push_assume("s2", "s.index(2) == 4");
    ctx.push_assume("s3", "s.index(3) == 3");
    ctx.push_assume("p0_def", "p0 == s.index(0)");
    ctx.push_assume("p1_def", "p1 == p0 + s.index(1)");
    ctx.push_assume("p2_def", "p2 == p1 + s.index(2)");
    ctx.push_assume("p3_def", "p3 == p2 + s.index(3)");

    ctx.push_assert(
        "p3_sum",
        "p3 == s.index(0) + s.index(1) + s.index(2) + s.index(3)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 19a: concrete prefix sum workaround should verify, got: {:?}",
        result,
    );
}

/// Tier 19a: Range sum query — sum(1..3) = prefix[2] - prefix[0].
///
/// prefix[0] = s[0], prefix[2] = s[0]+s[1]+s[2].
/// Prove: prefix[2] - prefix[0] == s[1] + s[2].
/// Requires cancelling the s[0] terms.
#[test]
fn test_vt_tier19a_prefix_range_query() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("p0", "i32");
    ctx.declare_var_parsed("p2", "i32");

    ctx.push_assume("s_len", "s.len() >= 3");
    ctx.push_assume("eb0", "s.index(0) >= -10000 && s.index(0) <= 10000");
    ctx.push_assume("eb1", "s.index(1) >= -10000 && s.index(1) <= 10000");
    ctx.push_assume("eb2", "s.index(2) >= -10000 && s.index(2) <= 10000");

    ctx.push_assume("p0_def", "p0 == s.index(0)");
    ctx.push_assume("p2_def", "p2 == s.index(0) + s.index(1) + s.index(2)");

    ctx.push_assert("range_sum", "p2 - p0 == s.index(1) + s.index(2)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 19a: range query should verify, got: {:?}",
        result,
    );
}

/// Tier 19a: Wrong recurrence — using s[0] instead of s[1] breaks sum.
#[test]
fn test_vt_tier19a_prefix_wrong_recurrence_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("p0", "i32");
    ctx.declare_var_parsed("p1", "i32");

    ctx.push_assume("s_len", "s.len() >= 2");
    ctx.push_assume("eb0", "s.index(0) >= -10000 && s.index(0) <= 10000");
    ctx.push_assume("eb1", "s.index(1) >= -10000 && s.index(1) <= 10000");

    // WRONG: p1 = p0 + s[0] instead of s[1]
    ctx.push_assume("p0_def", "p0 == s.index(0)");
    ctx.push_assume("p1_wrong", "p1 == p0 + s.index(0)");

    // p1 = 2*s[0] != s[0] + s[1] when s[0] != s[1]
    ctx.push_assert("p1_sum", "p1 == s.index(0) + s.index(1)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 19a negative: wrong recurrence (e.g. s[0]=1, s[1]=2 so p1=2 != 3) should produce a counterexample, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Dutch National Flag (3-way partition)
//
// Partition array around pivot p into three regions:
//   [0, lo): elements < p
//   [lo, hi): elements == p
//   [hi, n): elements > p
//
// Competition pattern: quicksort partition, classification problems.
// ========================================================================

/// Tier 19b: Concrete partition — verify element ordering holds.
///
/// Array [1, 3, 3, 5, 7] around pivot 3: lo=1, hi=3.
/// All 5 ordering constraints checked.
#[test]
fn test_vt_tier19b_dnf_concrete_partition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("pivot", "i32");

    ctx.push_assume("len5", "s.len() == 5");
    ctx.push_assume("pivot_val", "pivot == 3");
    ctx.push_assume("s0", "s.index(0) == 1");
    ctx.push_assume("s1", "s.index(1) == 3");
    ctx.push_assume("s2", "s.index(2) == 3");
    ctx.push_assume("s3", "s.index(3) == 5");
    ctx.push_assume("s4", "s.index(4) == 7");

    ctx.push_assert("lo_region", "s.index(0) < pivot");
    ctx.push_assert("mid_region_1", "s.index(1) == pivot");
    ctx.push_assert("mid_region_2", "s.index(2) == pivot");
    ctx.push_assert("hi_region_3", "s.index(3) > pivot");
    ctx.push_assert("hi_region_4", "s.index(4) > pivot");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 19b: concrete DNF partition should verify, got: {:?}",
        result,
    );
}

/// Tier 19b: DNF step — classify element < pivot, extend low region.
///
/// Given partition (lo=1, hi=3) over 4 elements, insert new_elem < pivot.
/// Result: [s[0], new_elem, s[1], s[2], s[3]] with lo=2, hi=4.
/// Requires transitive reasoning through equalities and inequalities.
#[test]
fn test_vt_tier19b_dnf_step_classify_low() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_new", "Seq<i32>");
    ctx.declare_var_parsed("pivot", "i32");
    ctx.declare_var_parsed("new_elem", "i32");

    ctx.push_assume("s_len", "s.len() == 4");
    ctx.push_assume("s_new_len", "s_new.len() == 5");

    // Existing partition: lo=1, hi=3
    ctx.push_assume("old_lo", "s.index(0) < pivot");
    ctx.push_assume("old_mid_1", "s.index(1) == pivot");
    ctx.push_assume("old_mid_2", "s.index(2) == pivot");
    ctx.push_assume("old_hi", "s.index(3) > pivot");

    ctx.push_assume("new_lt", "new_elem < pivot");

    // Insert into low region: s_new = [s[0], new_elem, s[1], s[2], s[3]]
    ctx.push_assume("new_0", "s_new.index(0) == s.index(0)");
    ctx.push_assume("new_1", "s_new.index(1) == new_elem");
    ctx.push_assume("new_2", "s_new.index(2) == s.index(1)");
    ctx.push_assume("new_3", "s_new.index(3) == s.index(2)");
    ctx.push_assume("new_4", "s_new.index(4) == s.index(3)");

    // New partition: lo=2, hi=4
    ctx.push_assert("new_lo_0", "s_new.index(0) < pivot");
    ctx.push_assert("new_lo_1", "s_new.index(1) < pivot");
    ctx.push_assert("new_mid_2", "s_new.index(2) == pivot");
    ctx.push_assert("new_mid_3", "s_new.index(3) == pivot");
    ctx.push_assert("new_hi_4", "s_new.index(4) > pivot");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 19b: DNF step (low) should verify, got: {:?}",
        result,
    );
}

/// Tier 19b: DNF step — classify element == pivot, extend mid region.
///
/// Insert new_elem == pivot between mid and hi regions.
#[test]
fn test_vt_tier19b_dnf_step_classify_mid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_new", "Seq<i32>");
    ctx.declare_var_parsed("pivot", "i32");
    ctx.declare_var_parsed("new_elem", "i32");

    ctx.push_assume("s_len", "s.len() == 4");
    ctx.push_assume("s_new_len", "s_new.len() == 5");

    ctx.push_assume("old_lo", "s.index(0) < pivot");
    ctx.push_assume("old_mid_1", "s.index(1) == pivot");
    ctx.push_assume("old_mid_2", "s.index(2) == pivot");
    ctx.push_assume("old_hi", "s.index(3) > pivot");

    ctx.push_assume("new_eq", "new_elem == pivot");

    // Append to mid: s_new = [s[0], s[1], s[2], new_elem, s[3]]
    ctx.push_assume("new_0", "s_new.index(0) == s.index(0)");
    ctx.push_assume("new_1", "s_new.index(1) == s.index(1)");
    ctx.push_assume("new_2", "s_new.index(2) == s.index(2)");
    ctx.push_assume("new_3", "s_new.index(3) == new_elem");
    ctx.push_assume("new_4", "s_new.index(4) == s.index(3)");

    // New partition: lo=1, hi=4
    ctx.push_assert("new_lo_0", "s_new.index(0) < pivot");
    ctx.push_assert("new_mid_1", "s_new.index(1) == pivot");
    ctx.push_assert("new_mid_2", "s_new.index(2) == pivot");
    ctx.push_assert("new_mid_3", "s_new.index(3) == pivot");
    ctx.push_assert("new_hi_4", "s_new.index(4) > pivot");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 19b: DNF step (mid) should verify, got: {:?}",
        result,
    );
}

/// Tier 19b: Wrong classification — element > pivot placed in mid region.
#[test]
fn test_vt_tier19b_dnf_wrong_classification_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s_new", "Seq<i32>");
    ctx.declare_var_parsed("pivot", "i32");
    ctx.declare_var_parsed("wrong_elem", "i32");

    ctx.push_assume("s_new_len", "s_new.len() == 3");
    ctx.push_assume("pivot_val", "pivot == 5");
    ctx.push_assume("wrong", "wrong_elem > pivot");
    ctx.push_assume("new_0", "s_new.index(0) == pivot");
    ctx.push_assume("new_1", "s_new.index(1) == wrong_elem");
    ctx.push_assume("new_2", "s_new.index(2) == pivot");

    // Mid region should all == pivot, but s_new[1] > pivot
    ctx.push_assert("mid_all_eq", "s_new.index(1) == pivot");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 19b negative: misclassifying an element above the pivot (e.g. pivot=5, wrong_elem=6) should produce a counterexample, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Element Counting
//
// Process array, counting elements satisfying a predicate (> 0).
// Invariant: count_pos + count_non == i (elements processed).
// Competition pattern: histogram, voting, classification problems.
// ========================================================================

/// Tier 19c: Counting init — classify first element, total == 1.
///
/// Disjunction: either s[0] > 0 (count_pos=1) or s[0] <= 0 (count_non=1).
/// In both cases, count_pos + count_non == 1.
#[test]
fn test_vt_tier19c_counting_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("count_pos", "u64");
    ctx.declare_var_parsed("count_non", "u64");

    ctx.push_assume("s_len", "s.len() >= 1");
    ctx.push_assume(
        "init",
        "(s.index(0) > 0 && count_pos == 1 && count_non == 0) || \
         (s.index(0) <= 0 && count_pos == 0 && count_non == 1)",
    );

    ctx.push_assert("total_1", "count_pos + count_non == 1");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 19c: counting init should verify, got: {:?}",
        result,
    );
}

/// Tier 19c: Counting step — classify s[i], total increases by 1.
///
/// Inductive step: given count_pos + count_non == i, after classifying
/// one more element, count_pos' + count_non' == i + 1.
/// Requires case analysis on the disjunction.
#[test]
fn test_vt_tier19c_counting_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("count_pos", "u64");
    ctx.declare_var_parsed("count_non", "u64");
    ctx.declare_var_parsed("count_pos_new", "u64");
    ctx.declare_var_parsed("count_non_new", "u64");
    ctx.declare_var_parsed("i", "u64");

    ctx.push_assume("s_len", "s.len() <= 1000");
    ctx.push_assume("i_bound", "i < s.len()");
    ctx.push_assume("i_small", "i < 999");
    ctx.push_assume("ih_total", "count_pos + count_non == i");

    ctx.push_assume(
        "classify",
        "(s.index(i) > 0 && count_pos_new == count_pos + 1 && count_non_new == count_non) || \
         (s.index(i) <= 0 && count_pos_new == count_pos && count_non_new == count_non + 1)",
    );

    ctx.push_assert("total_step", "count_pos_new + count_non_new == i + 1");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 19c: counting step should verify, got: {:?}",
        result,
    );
}

/// Tier 19c: Counting exit — concrete 4-element execution derives final counts.
///
/// Execute 4 classification steps: s = [+, -, +, +].
/// Chain step0→step3 to derive cp3==3, cn3==1, total==4.
/// Removing any step assumption breaks the proof.
#[test]
fn test_vt_tier19c_counting_exit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("cp0", "u64");
    ctx.declare_var_parsed("cn0", "u64");
    ctx.declare_var_parsed("cp1", "u64");
    ctx.declare_var_parsed("cn1", "u64");
    ctx.declare_var_parsed("cp2", "u64");
    ctx.declare_var_parsed("cn2", "u64");
    ctx.declare_var_parsed("cp3", "u64");
    ctx.declare_var_parsed("cn3", "u64");

    ctx.push_assume("s_len", "s.len() == 4");

    // Step 0: s[0] > 0
    ctx.push_assume("s0_pos", "s.index(0) > 0");
    ctx.push_assume("step0", "cp0 == 1 && cn0 == 0");

    // Step 1: s[1] <= 0
    ctx.push_assume("s1_neg", "s.index(1) <= 0");
    ctx.push_assume("step1", "cp1 == cp0 && cn1 == cn0 + 1");

    // Step 2: s[2] > 0
    ctx.push_assume("s2_pos", "s.index(2) > 0");
    ctx.push_assume("step2", "cp2 == cp1 + 1 && cn2 == cn1");

    // Step 3: s[3] > 0
    ctx.push_assume("s3_pos", "s.index(3) > 0");
    ctx.push_assume("step3", "cp3 == cp2 + 1 && cn3 == cn2");

    ctx.push_assert("total_4", "cp3 + cn3 == 4");
    ctx.push_assert("count_pos_3", "cp3 == 3");
    ctx.push_assert("count_non_1", "cn3 == 1");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 19c: counting exit should verify, got: {:?}",
        result,
    );
}

/// Tier 19c: Wrong classification — positive element not counted.
///
/// If elem > 0 but count_pos stays the same, the individual count is wrong.
#[test]
fn test_vt_tier19c_counting_wrong_classify_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("count_pos", "u64");
    ctx.declare_var_parsed("count_non", "u64");
    ctx.declare_var_parsed("count_pos_new", "u64");
    ctx.declare_var_parsed("count_non_new", "u64");
    ctx.declare_var_parsed("elem", "i32");

    ctx.push_assume("count_small", "count_pos < 1000 && count_non < 1000");
    ctx.push_assume("elem_pos", "elem > 0");

    // WRONG: increment count_non instead of count_pos for positive element
    ctx.push_assume(
        "wrong",
        "count_pos_new == count_pos && count_non_new == count_non + 1",
    );

    // count_pos should have increased
    ctx.push_assert("pos_increased", "count_pos_new > count_pos");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 19c negative: leaving count_pos unchanged for elem=1 should produce a counterexample, got: {:?}",
        result,
    );
}
