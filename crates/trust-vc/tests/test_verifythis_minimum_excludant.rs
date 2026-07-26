// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 28 - Minimum Excludant practice problem.
//!
//! Modeled from VerifyThis 2025 Challenge 1 "Minimum Excludant", focusing on
//! the sorted-array variant (`mex3`): in a sorted sequence of distinct
//! non-negative integers, the minimum excludant is the first index where
//! `s[i] != i`, or `len` when there is no gap.
//!
//! These tests exercise the real competition shape:
//! 1. Loop-step invariant preservation: `forall j < i. s[j] == j`
//! 2. Front-gap exit: first element already exceeds zero
//! 3. Interior-gap exit: prefix matches identity, then a gap appears
//! 4. No-gap exit: the sequence is exactly `[0, 1, ..., n - 1]`
//! 5. Negative checks: wrong candidates must be rejected
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

/// Tier 28a: scanning step preserves the identity-prefix invariant.
///
/// If the prefix `0..i` already satisfies `s[j] == j` and the current element
/// also matches (`s[i] == i`), then incrementing the scan index preserves
/// `forall j < i + 1. s[j] == j`.
#[test]
fn test_vt_tier28a_mex_prefix_step_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<u64>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("i_new", "u64");

    ctx.push_assume("len4", "s.len() == 4");
    ctx.push_assume("i_lt_3", "i < 3");
    ctx.push_assume(
        "prefix_identity",
        "forall(|j: u64| !(j < i) || s.index(j) == j)",
    );
    ctx.push_assume("current_matches", "s.index(i) == i");
    ctx.push_assume("step", "i_new == i + 1");

    ctx.push_assert(
        "prefix_identity_preserved",
        "forall(|j: u64| !(j < i_new) || s.index(j) == j)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 28a: MEX prefix-step invariant should verify, got: {:?}",
        result,
    );
}

/// Tier 28b: front gap means `mex = 0`.
///
/// Concrete sorted sequence `[2, 4, 7]`: zero is absent, so the minimum
/// excludant is zero.
#[test]
fn test_vt_tier28b_mex_front_gap_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<u64>");
    ctx.declare_var_parsed("mex", "u64");

    ctx.push_assume("len3", "s.len() == 3");
    ctx.push_assume("s0", "s.index(0) == 2");
    ctx.push_assume("s1", "s.index(1) == 4");
    ctx.push_assume("s2", "s.index(2) == 7");
    ctx.push_assume("mex_zero", "mex == 0");

    ctx.push_assert(
        "mex_absent",
        "forall(|j: u64| !(j < 3) || s.index(j) != mex)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 28b: front-gap MEX should verify, got: {:?}",
        result,
    );
}

/// Tier 28c: first interior gap determines the MEX.
///
/// Concrete sorted sequence `[0, 1, 3]`: the prefix matches identity up to 2
/// and element 2 is already larger than 2, so `mex = 2`.
#[test]
fn test_vt_tier28c_mex_interior_gap_is_index() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<u64>");
    ctx.declare_var_parsed("mex", "u64");

    ctx.push_assume("len3", "s.len() == 3");
    ctx.push_assume("s0", "s.index(0) == 0");
    ctx.push_assume("s1", "s.index(1) == 1");
    ctx.push_assume("s2", "s.index(2) == 3");
    ctx.push_assume("mex_two", "mex == 2");

    ctx.push_assert(
        "prefix_identity",
        "forall(|j: u64| !(j < mex) || s.index(j) == j)",
    );
    ctx.push_assert(
        "mex_absent",
        "forall(|j: u64| !(j < 3) || s.index(j) != mex)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 28c: interior-gap MEX should verify, got: {:?}",
        result,
    );
}

/// Tier 28d: no gap means `mex = len`.
///
/// If the sorted sequence is exactly `[0, 1, ..., n - 1]`, then `n` itself is
/// the first excluded value.
#[test]
fn test_vt_tier28d_mex_no_gap_returns_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<u64>");
    ctx.declare_var_parsed("mex", "u64");

    ctx.push_assume("len3", "s.len() == 3");
    ctx.push_assume("s0", "s.index(0) == 0");
    ctx.push_assume("s1", "s.index(1) == 1");
    ctx.push_assume("s2", "s.index(2) == 2");
    ctx.push_assume("mex_is_len", "mex == 3");

    ctx.push_assert(
        "mex_absent",
        "forall(|j: u64| !(j < 3) || s.index(j) != mex)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 28d: no-gap exit should verify, got: {:?}",
        result,
    );
}

/// Tier 28e: claiming the next present element as MEX must fail.
#[test]
fn test_vt_tier28e_mex_wrong_interior_candidate_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<u64>");
    ctx.declare_var_parsed("mex", "u64");

    ctx.push_assume("len3", "s.len() == 3");
    ctx.push_assume("s0", "s.index(0) == 0");
    ctx.push_assume("s1", "s.index(1) == 1");
    ctx.push_assume("s2", "s.index(2) == 3");
    ctx.push_assume("mex_three", "mex == 3");

    ctx.push_assert(
        "mex_absent_false",
        "forall(|j: u64| !(j < 3) || s.index(j) != mex)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 28e SOUNDNESS: present value must not verify as MEX, got: {:?}",
        result,
    );
}

/// Tier 28f: in the no-gap case, any `mex < len` is wrong because it is present.
#[test]
fn test_vt_tier28f_mex_wrong_no_gap_candidate_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<u64>");
    ctx.declare_var_parsed("mex", "u64");

    ctx.push_assume("len3", "s.len() == 3");
    ctx.push_assume("s0", "s.index(0) == 0");
    ctx.push_assume("s1", "s.index(1) == 1");
    ctx.push_assume("s2", "s.index(2) == 2");
    ctx.push_assume("mex_two", "mex == 2");

    ctx.push_assert(
        "mex_absent_false",
        "forall(|j: u64| !(j < 3) || s.index(j) != mex)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 28f SOUNDNESS: no-gap case must reject mex < len, got: {:?}",
        result,
    );
}
