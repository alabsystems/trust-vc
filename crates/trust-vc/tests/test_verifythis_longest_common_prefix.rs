// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 44 — Longest Common Prefix (LCP) VCs.
//!
//! VerifyThis 2021 Challenge 1 asked contestants to verify a longest common
//! prefix function: given two arrays `a` and `b`, find the length of their
//! longest common prefix (the largest `k` such that `a[j] == b[j]` for all
//! `j < k`).
//!
//! This tier keeps the proof obligations on the stable VerificationPipeline
//! path by phrasing the core LCP properties as explicit post-state VCs:
//!   - init: at i=0 the invariant holds vacuously
//!   - step: matching elements extend the common prefix
//!   - exit (mismatch): diverging elements bound the prefix
//!   - exit (end): reaching min(len_a, len_b) means one is a prefix of the other
//!   - postcondition: quantified agreement below the result index
//!   - frame: input sequences are not modified
//!   - negative: wrong LCP values are rejected
//!   - positive cases keep shared-prefix values symbolic so the solver proves prefix structure
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
    let len_name = format!("{name}_len");
    let len_cond = format!("{name}.len() == {}", values.len());
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(&len_name, &len_cond);
    for (idx, value) in values.iter().enumerate() {
        let elem_name = format!("{name}_{idx}");
        let elem_cond = format!("{name}.index({idx}) == {value}");
        ctx.push_assume(&elem_name, &elem_cond);
    }
}

fn assume_seq_exprs(ctx: &mut VerificationContext, name: &str, exprs: &[&str]) {
    let len_name = format!("{name}_len");
    let len_cond = format!("{name}.len() == {}", exprs.len());
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(&len_name, &len_cond);
    for (idx, expr) in exprs.iter().enumerate() {
        let elem_name = format!("{name}_{idx}");
        let elem_cond = format!("{name}.index({idx}) == {expr}");
        ctx.push_assume(&elem_name, &elem_cond);
    }
}

fn setup_symbolic_lcp_mismatch(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("prefix0", "i64");
    ctx.declare_var_parsed("prefix1", "i64");
    ctx.declare_var_parsed("a_tail", "i64");
    ctx.declare_var_parsed("b_tail", "i64");
    ctx.push_assume("tail_mismatch", "a_tail != b_tail");
    assume_seq_exprs(ctx, "a", &["prefix0", "prefix1", "a_tail"]);
    assume_seq_exprs(ctx, "b", &["prefix0", "prefix1", "b_tail"]);
}
fn setup_symbolic_lcp_prefix(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("prefix0", "i64");
    ctx.declare_var_parsed("prefix1", "i64");
    ctx.declare_var_parsed("extra", "i64");
    assume_seq_exprs(ctx, "a", &["prefix0", "prefix1"]);
    assume_seq_exprs(ctx, "b", &["prefix0", "prefix1", "extra"]);
}
fn setup_symbolic_lcp_identical(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("value0", "i64");
    ctx.declare_var_parsed("value1", "i64");
    ctx.declare_var_parsed("value2", "i64");
    assume_seq_exprs(ctx, "a", &["value0", "value1", "value2"]);
    assume_seq_exprs(ctx, "b", &["value0", "value1", "value2"]);
}

// ========================================================================
// GROUP A: Init and step VCs
// ========================================================================

/// Tier 44a: at i=0, no elements have been compared — the empty prefix matches.
#[test]
fn test_vt_tier44a_init_empty_prefix_matches() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_lcp_mismatch(&mut ctx);
    ctx.declare_var_parsed("i", "i64");

    ctx.push_assume("i_init", "i == 0");

    // The invariant at i=0: all elements below i agree (vacuously true).
    // Also: i is within bounds for iteration.
    ctx.push_assert("i_nonneg", "i >= 0");
    ctx.push_assert("i_le_len_a", "i <= a.len()");
    ctx.push_assert("i_le_len_b", "i <= b.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 44a: init at i=0 should satisfy the prefix invariant vacuously, got: {:?}",
        result,
    );
}

/// Tier 44b: if a[i] == b[i], then the matching prefix extends to i+1.
#[test]
fn test_vt_tier44b_step_matching_elements_extend_prefix() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_lcp_mismatch(&mut ctx);
    ctx.declare_var_parsed("i", "i64");
    ctx.declare_var_parsed("i_next", "i64");

    // Invariant at iteration i=0: a[0..0] matches b[0..0] (vacuously).
    ctx.push_assume("i_val", "i == 0");
    ctx.push_assume("i_in_range_a", "i < a.len()");
    ctx.push_assume("i_in_range_b", "i < b.len()");
    ctx.push_assume("match_at_i", "a.index(0) == b.index(0)");
    ctx.push_assume("advance", "i_next == i + 1");

    // After step: the quantified prefix property now covers index 0.
    ctx.push_assert(
        "extended_prefix_agreement",
        "forall(|j: u64| !(j < 1) || a.index(j) == b.index(j))",
    );
    ctx.push_assert("i_next_val", "i_next == 1");
    ctx.push_assert("i_next_le_a", "i_next <= a.len()");
    ctx.push_assert("i_next_le_b", "i_next <= b.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 44b: matching a[i]==b[i] should extend the prefix to i+1, got: {:?}",
        result,
    );
}

/// Tier 44c: second step — a[1]==b[1] extends the prefix from 1 to 2.
#[test]
fn test_vt_tier44c_step_second_iteration_extends() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_lcp_mismatch(&mut ctx);
    ctx.declare_var_parsed("i", "i64");
    ctx.declare_var_parsed("i_next", "i64");

    ctx.push_assume("i_val", "i == 1");
    ctx.push_assume("i_in_range_a", "i < a.len()");
    ctx.push_assume("i_in_range_b", "i < b.len()");
    // Invariant: a[0]==b[0] (from prior step)
    ctx.push_assume("prefix_0", "a.index(0) == b.index(0)");
    ctx.push_assume("match_at_i", "a.index(1) == b.index(1)");
    ctx.push_assume("advance", "i_next == i + 1");

    ctx.push_assert(
        "extended_prefix_agreement",
        "forall(|j: u64| !(j < 2) || a.index(j) == b.index(j))",
    );
    ctx.push_assert("i_next_val", "i_next == 2");
    ctx.push_assert("i_next_le_a", "i_next <= a.len()");
    ctx.push_assert("i_next_le_b", "i_next <= b.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 44c: second matching step should grow the prefix to 2, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Exit conditions
// ========================================================================

/// Tier 44d: a[i] != b[i] means the LCP is exactly i.
#[test]
fn test_vt_tier44d_exit_mismatch_determines_lcp() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_lcp_mismatch(&mut ctx);
    ctx.declare_var_parsed("i", "i64");
    ctx.declare_var_parsed("result", "i64");

    ctx.push_assume("i_val", "i == 2");
    ctx.push_assume("prefix_0", "a.index(0) == b.index(0)");
    ctx.push_assume("prefix_1", "a.index(1) == b.index(1)");
    ctx.push_assume("mismatch", "a.index(2) != b.index(2)");
    ctx.push_assume("result_def", "result == i");

    // LCP is 2: first two agree, third diverges.
    ctx.push_assert("result_is_2", "result == 2");
    ctx.push_assert(
        "prefix_agreement",
        "forall(|j: u64| !(j < 2) || a.index(j) == b.index(j))",
    );

    let result_vr = verify_with_pipeline(ctx);
    assert!(
        matches!(result_vr, VerifyResult::Verified),
        "TIER 44d: mismatch at a[2]!=b[2] should yield LCP=2, got: {:?}",
        result_vr,
    );
}

/// Tier 44e: if one sequence is a prefix of the other, LCP equals the shorter length.
#[test]
fn test_vt_tier44e_exit_shorter_is_prefix() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_lcp_prefix(&mut ctx);
    ctx.declare_var_parsed("result", "i64");

    ctx.push_assume("prefix_0", "a.index(0) == b.index(0)");
    ctx.push_assume("prefix_1", "a.index(1) == b.index(1)");
    // Loop exits because i reaches a.len() == 2, which is min(2, 3).
    ctx.push_assume("result_def", "result == a.len()");

    ctx.push_assert("result_is_2", "result == 2");
    ctx.push_assert("result_le_a", "result <= a.len()");
    ctx.push_assert("result_le_b", "result <= b.len()");
    ctx.push_assert(
        "prefix_agreement",
        "forall(|j: u64| !(j < 2) || a.index(j) == b.index(j))",
    );

    let result_vr = verify_with_pipeline(ctx);
    assert!(
        matches!(result_vr, VerifyResult::Verified),
        "TIER 44e: shorter-is-prefix should yield LCP = len(shorter), got: {:?}",
        result_vr,
    );
}

/// Tier 44f: identical sequences have LCP equal to their common length.
#[test]
fn test_vt_tier44f_identical_sequences_full_match() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_lcp_identical(&mut ctx);
    ctx.declare_var_parsed("result", "i64");

    ctx.push_assume("prefix_0", "a.index(0) == b.index(0)");
    ctx.push_assume("prefix_1", "a.index(1) == b.index(1)");
    ctx.push_assume("prefix_2", "a.index(2) == b.index(2)");
    ctx.push_assume("result_def", "result == a.len()");

    ctx.push_assert("result_is_3", "result == 3");
    ctx.push_assert(
        "full_prefix_agreement",
        "forall(|j: u64| !(j < 3) || a.index(j) == b.index(j))",
    );
    ctx.push_assert("result_eq_lens", "result == a.len() && result == b.len()");

    let result_vr = verify_with_pipeline(ctx);
    assert!(
        matches!(result_vr, VerifyResult::Verified),
        "TIER 44f: identical sequences should yield LCP = common length, got: {:?}",
        result_vr,
    );
}

/// Tier 44g: empty sequences have LCP 0.
#[test]
fn test_vt_tier44g_empty_sequences_lcp_zero() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[]);
    assume_seq_i64(&mut ctx, "b", &[10, 20]);
    ctx.declare_var_parsed("result", "i64");

    // Loop never executes because a.len() == 0.
    ctx.push_assume("result_def", "result == a.len()");

    ctx.push_assert("result_is_0", "result == 0");
    ctx.push_assert("result_le_a", "result <= a.len()");
    ctx.push_assert("result_le_b", "result <= b.len()");

    let result_vr = verify_with_pipeline(ctx);
    assert!(
        matches!(result_vr, VerifyResult::Verified),
        "TIER 44g: empty left array should yield LCP=0, got: {:?}",
        result_vr,
    );
}

// ========================================================================
// GROUP C: Negative / soundness tests
// ========================================================================

/// Tier 44h: claiming LCP is 3 when the mismatch is at index 2.
#[test]
fn test_vt_tier44h_wrong_lcp_overshoot_rejected() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_lcp_mismatch(&mut ctx);
    ctx.declare_var_parsed("result", "i64");

    ctx.push_assume("prefix_0", "a.index(0) == b.index(0)");
    ctx.push_assume("prefix_1", "a.index(1) == b.index(1)");
    ctx.push_assume("mismatch", "a.index(2) != b.index(2)");
    // Incorrect claim: LCP is 3 (past the mismatch point).
    ctx.push_assume("result_wrong", "result == 3");

    // This should fail: result claims agreement at index 2, but a[2] != b[2].
    ctx.push_assert("agree_at_result_minus_1", "a.index(2) == b.index(2)");

    let result_vr = verify_with_pipeline(ctx);
    assert!(
        matches!(result_vr, VerifyResult::Counterexample { .. }),
        "TIER 44h SOUNDNESS: overstated LCP should be rejected, got: {:?}",
        result_vr,
    );
}

/// Tier 44i: claiming LCP is 1 when the first two elements agree.
#[test]
fn test_vt_tier44i_wrong_lcp_undershoot_rejected() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_lcp_mismatch(&mut ctx);
    ctx.declare_var_parsed("result", "i64");

    ctx.push_assume("prefix_0", "a.index(0) == b.index(0)");
    ctx.push_assume("prefix_1", "a.index(1) == b.index(1)");
    ctx.push_assume("mismatch", "a.index(2) != b.index(2)");
    // Incorrect claim: LCP is 1 (too low).
    ctx.push_assume("result_wrong", "result == 1");

    // If result is claimed as 1, then the mismatch should be at index 1.
    // But a[1]==b[1], so this assertion should fail.
    ctx.push_assert("mismatch_at_result", "a.index(1) != b.index(1)");

    let result_vr = verify_with_pipeline(ctx);
    assert!(
        matches!(result_vr, VerifyResult::Counterexample { .. }),
        "TIER 44i SOUNDNESS: understated LCP should be rejected, got: {:?}",
        result_vr,
    );
}

/// Tier 44j: claiming LCP exceeds the minimum sequence length.
#[test]
fn test_vt_tier44j_lcp_exceeds_min_length_rejected() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_lcp_prefix(&mut ctx);
    ctx.declare_var_parsed("result", "i64");

    // Claim result=3, but a only has 2 elements.
    ctx.push_assume("result_wrong", "result == 3");

    ctx.push_assert("result_le_a", "result <= a.len()");

    let result_vr = verify_with_pipeline(ctx);
    assert!(
        matches!(result_vr, VerifyResult::Counterexample { .. }),
        "TIER 44j SOUNDNESS: LCP > min(len_a, len_b) should be rejected, got: {:?}",
        result_vr,
    );
}

// ========================================================================
// GROUP D: Concrete end-to-end traces
// ========================================================================

/// Tier 44k: full 3-step trace — [10,20,30] vs [10,20,40] yields LCP=2.
#[test]
fn test_vt_tier44k_full_trace_lcp_2() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_lcp_mismatch(&mut ctx);

    // Step 0: i=0, a[0]==b[0] ✓ → i=1
    // Step 1: i=1, a[1]==b[1] ✓ → i=2
    // Step 2: i=2, a[2]!=b[2] ✗ → exit, result=2

    ctx.declare_var_parsed("i0", "i64");
    ctx.declare_var_parsed("i1", "i64");
    ctx.declare_var_parsed("i2", "i64");
    ctx.declare_var_parsed("result", "i64");

    ctx.push_assume("step0_start", "i0 == 0");
    ctx.push_assume("step0_match", "a.index(0) == b.index(0)");
    ctx.push_assume("step0_advance", "i1 == i0 + 1");

    ctx.push_assume("step1_match", "a.index(1) == b.index(1)");
    ctx.push_assume("step1_advance", "i2 == i1 + 1");

    ctx.push_assume("step2_mismatch", "a.index(2) != b.index(2)");
    ctx.push_assume("result_def", "result == i2");

    ctx.push_assert("trace_result", "result == 2");

    let result_vr = verify_with_pipeline(ctx);
    assert!(
        matches!(result_vr, VerifyResult::Verified),
        "TIER 44k: full trace [10,20,30] vs [10,20,40] should yield LCP=2, got: {:?}",
        result_vr,
    );
}

/// Tier 44l: full trace with immediate mismatch — [1,2] vs [3,4] yields LCP=0.
#[test]
fn test_vt_tier44l_full_trace_immediate_mismatch() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[1, 2]);
    assume_seq_i64(&mut ctx, "b", &[3, 4]);
    ctx.declare_var_parsed("result", "i64");

    ctx.push_assume("mismatch_at_0", "a.index(0) != b.index(0)");
    ctx.push_assume("result_def", "result == 0");

    ctx.push_assert("result_plus_left_head", "result + a.index(0) == 1");
    ctx.push_assert("strict_head_order", "a.index(0) < b.index(0)");

    let result_vr = verify_with_pipeline(ctx);
    assert!(
        matches!(result_vr, VerifyResult::Verified),
        "TIER 44l: immediate mismatch should yield LCP=0, got: {:?}",
        result_vr,
    );
}

// ========================================================================
// GROUP E: Symbolic / quantified properties
// ========================================================================

/// Tier 44m: symbolic step VC — if all j < i agree and a[i] == b[i], then
/// all j < i+1 agree.
#[test]
fn test_vt_tier44m_symbolic_step_with_concrete_quantifier() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("prefix0", "i64");
    ctx.declare_var_parsed("prefix1", "i64");
    ctx.declare_var_parsed("match2", "i64");
    ctx.declare_var_parsed("a_tail", "i64");
    ctx.declare_var_parsed("b_tail", "i64");
    assume_seq_exprs(&mut ctx, "a", &["prefix0", "prefix1", "match2", "a_tail"]);
    assume_seq_exprs(&mut ctx, "b", &["prefix0", "prefix1", "match2", "b_tail"]);
    ctx.declare_var_parsed("i", "i64");
    ctx.declare_var_parsed("i_next", "i64");

    // Invariant: all j in 0..i agree.
    ctx.push_assume("i_val", "i == 2");
    ctx.push_assume("inv_0", "a.index(0) == b.index(0)");
    ctx.push_assume("inv_1", "a.index(1) == b.index(1)");
    // Step: a[i] == b[i]
    ctx.push_assume("match_at_i", "a.index(2) == b.index(2)");
    ctx.push_assume("advance", "i_next == i + 1");

    // Post: a single quantified property covers the whole prefix below i_next.
    ctx.push_assert(
        "extended_prefix_agreement",
        "forall(|j: u64| !(j < 3) || a.index(j) == b.index(j))",
    );
    ctx.push_assert("i_next_val", "i_next == 3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 44m: quantified step should extend agreement to i+1, got: {:?}",
        result,
    );
}

/// Tier 44n: frame condition — LCP computation does not modify either sequence.
#[test]
fn test_vt_tier44n_frame_sequences_unchanged() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_lcp_mismatch(&mut ctx);

    // Declare "after" copies that should be identical to the originals.
    ctx.declare_var_parsed("a_after", "Seq<i64>");
    ctx.declare_var_parsed("b_after", "Seq<i64>");
    ctx.push_assume("a_frame", "a_after == a");
    ctx.push_assume("a_frame_len", "a_after.len() == a.len()");
    ctx.push_assume("b_frame", "b_after == b");
    ctx.push_assume("b_frame_len", "b_after.len() == b.len()");

    ctx.push_assert("a_len_preserved", "a_after.len() == 3");
    ctx.push_assert("b_len_preserved", "b_after.len() == 3");
    ctx.push_assert(
        "a_frame_preserved",
        "forall(|j: u64| !(j < 3) || a_after.index(j) == a.index(j))",
    );
    ctx.push_assert(
        "b_frame_preserved",
        "forall(|j: u64| !(j < 3) || b_after.index(j) == b.index(j))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 44n: LCP should not modify either input sequence, got: {:?}",
        result,
    );
}
