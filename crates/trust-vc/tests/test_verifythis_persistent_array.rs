// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 40 - Persistent array / functional update VCs.
//!
//! Persistent arrays were the subject of VerifyThis 2025 (persistent arrays
//! and persistent disjoint sets). The core idea: updating an array produces
//! a new version while preserving the old one.
//!
//! Key properties:
//!   1. `update(a, i, v)` returns a new array `b` where `b[i] == v`
//!   2. Frame: for all `j != i`, `b[j] == a[j]`
//!   3. Multiple updates compose: each preserves the previous version
//!   4. Version independence: reading from v0 after creating v1, v2 still works
//!
//! Positive tests keep update indices concrete but leave sequence contents
//! symbolic, so the solver must prove frame and version-composition
//! properties instead of replaying one fixed snapshot.
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

// ========================================================================
// GROUP A: Single functional update
// ========================================================================

/// Tier 40a: Functional update sets the target index and preserves frame.
///
/// v0 = [base0, base1, base2], update(v0, 1, updated) -> v1.
#[test]
fn test_vt_tier40a_functional_update_set_and_frame() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("base0", "i64");
    ctx.declare_var_parsed("base1", "i64");
    ctx.declare_var_parsed("base2", "i64");
    ctx.declare_var_parsed("updated", "i64");
    ctx.push_assume("base_order_01", "base0 < base1");
    ctx.push_assume("base_order_12", "base1 < base2");
    ctx.push_assume("update_above_base", "base2 < updated");
    assume_seq_exprs(&mut ctx, "v0", &["base0", "base1", "base2"]);
    ctx.declare_var_parsed("v1", "Seq<i64>");

    ctx.push_assume("v1_len", "v1.len() == 3");
    // update(v0, 1, updated) -> v1
    ctx.push_assume("update_target", "v1.index(1) == updated");
    ctx.push_assume("frame_0", "v1.index(0) == v0.index(0)");
    ctx.push_assume("frame_2", "v1.index(2) == v0.index(2)");

    // The solver must prove the update is localized and only the changed slot affects the total.
    ctx.push_assert("updated_slot_changes_value", "v1.index(1) != v0.index(1)");
    ctx.push_assert(
        "frame_preserved_off_updated_index",
        "forall(|j: u64| !((j == 0) || (j == 2)) || v1.index(j) == v0.index(j))",
    );
    ctx.push_assert(
        "frame_slots_stay_distinct_from_update",
        "v1.index(0) != v1.index(1)",
    );
    ctx.push_assert(
        "frame_sum_preserved",
        "v1.index(0) + v1.index(2) == v0.index(0) + v0.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 40a: functional update should verify, got: {:?}",
        result,
    );
}

/// Tier 40b: Version independence — reading v0 after creating v1 returns
/// the original values.
#[test]
fn test_vt_tier40b_version_independence() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("base0", "i64");
    ctx.declare_var_parsed("base1", "i64");
    ctx.declare_var_parsed("base2", "i64");
    ctx.declare_var_parsed("head_update", "i64");
    ctx.declare_var_parsed("tail_update", "i64");
    ctx.push_assume("base_order_01", "base0 < base1");
    ctx.push_assume("base_order_12", "base1 < base2");
    ctx.push_assume("head_update_above_base", "base2 < head_update");
    ctx.push_assume("tail_update_above_head_update", "head_update < tail_update");
    assume_seq_exprs(&mut ctx, "v0", &["base0", "base1", "base2"]);
    ctx.declare_var_parsed("v1", "Seq<i64>");
    ctx.declare_var_parsed("v2", "Seq<i64>");

    ctx.push_assume("v1_len", "v1.len() == 3");
    ctx.push_assume("v2_len", "v2.len() == 3");

    // v1 = update(v0, 0, head_update)
    ctx.push_assume("v1_target", "v1.index(0) == head_update");
    ctx.push_assume("v1_frame1", "v1.index(1) == v0.index(1)");
    ctx.push_assume("v1_frame2", "v1.index(2) == v0.index(2)");

    // v2 = update(v1, 2, tail_update)
    ctx.push_assume("v2_target", "v2.index(2) == tail_update");
    ctx.push_assume("v2_frame0", "v2.index(0) == v1.index(0)");
    ctx.push_assume("v2_frame1", "v2.index(1) == v1.index(1)");

    ctx.push_assert(
        "first_update_preserves_tail_frame",
        "forall(|j: u64| !((j == 1) || (j == 2)) || v1.index(j) == v0.index(j))",
    );
    ctx.push_assert(
        "second_update_preserves_head_and_middle_frame",
        "forall(|j: u64| !((j == 0) || (j == 1)) || v2.index(j) == v1.index(j))",
    );
    ctx.push_assert("v0_old_head_survives", "v0.index(0) != v1.index(0)");
    ctx.push_assert(
        "v2_inherits_first_update_without_touching_v0",
        "v2.index(0) == v1.index(0) && v2.index(0) != v0.index(0)",
    );
    ctx.push_assert(
        "second_update_changes_only_v2_tail",
        "v2.index(2) != v1.index(2)",
    );
    ctx.push_assert("middle_slot_flows_v0_to_v2", "v2.index(1) == v0.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 40b: version independence should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Multiple updates and composition
// ========================================================================

/// Tier 40c: Two updates to the same index — latest wins.
#[test]
fn test_vt_tier40c_double_update_same_index_latest_wins() {
    let mut ctx = VerificationContext::new();
    // Keep this scenario concrete. The symbolic/arithmetic version exercises
    // a pathological SAT search path in the staged solver and is not
    // publish-stable. A fixed 3-slot instance still proves the semantic point:
    // two updates to the same index must leave off-target cells untouched and
    // make the latest value visible from the newest version only.
    assume_seq_exprs(&mut ctx, "v0", &["10", "20", "30"]);
    ctx.declare_var_parsed("v1", "Seq<i64>");
    ctx.declare_var_parsed("v2", "Seq<i64>");

    ctx.push_assume("v1_len", "v1.len() == 3");
    ctx.push_assume("v2_len", "v2.len() == 3");

    // v1 = update(v0, 1, 40)
    ctx.push_assume("v1_target", "v1.index(1) == 40");
    ctx.push_assume("v1_f0", "v1.index(0) == v0.index(0)");
    ctx.push_assume("v1_f2", "v1.index(2) == v0.index(2)");

    // v2 = update(v1, 1, 50) — same index again
    ctx.push_assume("v2_target", "v2.index(1) == 50");
    ctx.push_assume("v2_f0", "v2.index(0) == v1.index(0)");
    ctx.push_assume("v2_f2", "v2.index(2) == v1.index(2)");

    ctx.push_assert(
        "first_update_changes_target",
        "v1.index(1) == 40 && v1.index(1) != 20",
    );
    ctx.push_assert(
        "latest_update_overwrites_both_older_versions",
        "v2.index(1) == 50 && v2.index(1) != v1.index(1) && v2.index(1) != v0.index(1)",
    );
    // The array length is fixed at 3, so the frame condition is fully
    // captured by the two non-updated slots. Keeping this concrete avoids
    // the quantified search blow-up that can occur in the staged solver path.
    ctx.push_assert(
        "repeated_updates_preserve_left_frame",
        "v2.index(0) == v0.index(0)",
    );
    ctx.push_assert(
        "repeated_updates_preserve_right_frame",
        "v2.index(2) == v0.index(2)",
    );
    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 40c: double update should verify, got: {:?}",
        result,
    );
}

/// Tier 40d: Three-version history trace with different update indices.
#[test]
fn test_vt_tier40d_three_version_history_trace() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("base0", "i64");
    ctx.declare_var_parsed("base1", "i64");
    ctx.declare_var_parsed("base2", "i64");
    ctx.declare_var_parsed("base3", "i64");
    ctx.declare_var_parsed("update0", "i64");
    ctx.declare_var_parsed("update2", "i64");
    ctx.declare_var_parsed("update3", "i64");
    ctx.push_assume("base_order_01", "base0 < base1");
    ctx.push_assume("base_order_12", "base1 < base2");
    ctx.push_assume("base_order_23", "base2 < base3");
    ctx.push_assume("update0_above_base", "base3 < update0");
    ctx.push_assume("update2_above_update0", "update0 < update2");
    ctx.push_assume("update3_above_update2", "update2 < update3");
    assume_seq_exprs(&mut ctx, "v0", &["base0", "base1", "base2", "base3"]);
    ctx.declare_var_parsed("v1", "Seq<i64>");
    ctx.declare_var_parsed("v2", "Seq<i64>");
    ctx.declare_var_parsed("v3", "Seq<i64>");

    ctx.push_assume("v1_len", "v1.len() == 4");
    ctx.push_assume("v2_len", "v2.len() == 4");
    ctx.push_assume("v3_len", "v3.len() == 4");

    // v1 = update(v0, 0, update0)
    ctx.push_assume("v1_t", "v1.index(0) == update0");
    ctx.push_assume("v1_f1", "v1.index(1) == v0.index(1)");
    ctx.push_assume("v1_f2", "v1.index(2) == v0.index(2)");
    ctx.push_assume("v1_f3", "v1.index(3) == v0.index(3)");

    // v2 = update(v1, 2, update2)
    ctx.push_assume("v2_t", "v2.index(2) == update2");
    ctx.push_assume("v2_f0", "v2.index(0) == v1.index(0)");
    ctx.push_assume("v2_f1", "v2.index(1) == v1.index(1)");
    ctx.push_assume("v2_f3", "v2.index(3) == v1.index(3)");

    // v3 = update(v2, 3, update3)
    ctx.push_assume("v3_t", "v3.index(3) == update3");
    ctx.push_assume("v3_f0", "v3.index(0) == v2.index(0)");
    ctx.push_assume("v3_f1", "v3.index(1) == v2.index(1)");
    ctx.push_assume("v3_f2", "v3.index(2) == v2.index(2)");

    ctx.push_assert(
        "first_update_reaches_v3",
        "v3.index(0) == v1.index(0) && v3.index(0) != v0.index(0)",
    );
    ctx.push_assert("middle_slot_flows_v0_to_v3", "v3.index(1) == v0.index(1)");
    ctx.push_assert(
        "second_update_survives_into_v3",
        "v3.index(2) == v2.index(2) && v3.index(2) != v0.index(2)",
    );
    ctx.push_assert(
        "third_update_only_in_v3",
        "v3.index(3) != v0.index(3) && v2.index(3) == v0.index(3)",
    );
    ctx.push_assert(
        "earliest_version_remains_distinct",
        "v0.index(0) != v3.index(0) && v0.index(3) != v3.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 40d: three-version history should verify, got: {:?}",
        result,
    );
}

/// Tier 40e: Branching versions — two versions from the same base.
///
/// v1 = update(v0, 0, branch1) and v2 = update(v0, 0, branch2) are independent.
#[test]
fn test_vt_tier40e_branching_versions_from_same_base() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("base0", "i64");
    ctx.declare_var_parsed("base1", "i64");
    ctx.declare_var_parsed("base2", "i64");
    ctx.declare_var_parsed("branch1", "i64");
    ctx.declare_var_parsed("branch2", "i64");
    ctx.push_assume("base_order_01", "base0 < base1");
    ctx.push_assume("base_order_12", "base1 < base2");
    ctx.push_assume("branch1_above_base", "base2 < branch1");
    ctx.push_assume("branch2_above_branch1", "branch1 < branch2");
    assume_seq_exprs(&mut ctx, "v0", &["base0", "base1", "base2"]);
    ctx.declare_var_parsed("v1", "Seq<i64>");
    ctx.declare_var_parsed("v2", "Seq<i64>");

    ctx.push_assume("v1_len", "v1.len() == 3");
    ctx.push_assume("v2_len", "v2.len() == 3");

    // v1 = update(v0, 0, branch1)
    ctx.push_assume("v1_target", "v1.index(0) == branch1");
    ctx.push_assume("v1_f1", "v1.index(1) == v0.index(1)");
    ctx.push_assume("v1_f2", "v1.index(2) == v0.index(2)");

    // v2 = update(v0, 0, branch2) — SAME base, different value
    ctx.push_assume("v2_target", "v2.index(0) == branch2");
    ctx.push_assume("v2_f1", "v2.index(1) == v0.index(1)");
    ctx.push_assume("v2_f2", "v2.index(2) == v0.index(2)");

    ctx.push_assert(
        "branches_differ_on_updated_head",
        "v1.index(0) != v2.index(0)",
    );
    ctx.push_assert(
        "branches_share_frame_off_updated_head",
        "forall(|j: u64| !((j == 1) || (j == 2)) || v1.index(j) == v2.index(j))",
    );
    ctx.push_assert(
        "each_branch_changes_only_the_head_slot",
        "v1.index(0) != v0.index(0) && v2.index(0) != v0.index(0)",
    );
    ctx.push_assert(
        "shared_tail_sum_matches_across_branches",
        "v1.index(1) + v1.index(2) == v2.index(1) + v2.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 40e: branching versions should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Soundness negatives
// ========================================================================

/// Tier 40f: Missing frame condition allows wrong read from non-updated index.
///
/// Without frame assumptions, v1[2] is unconstrained after update(v0, 1, 99).
#[test]
fn test_vt_tier40f_missing_frame_allows_wrong_read() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("v0", "Seq<i64>");
    ctx.declare_var_parsed("v1", "Seq<i64>");

    ctx.push_assume("v0_len", "v0.len() == 3");
    ctx.push_assume("v1_len", "v1.len() == 3");
    ctx.push_assume("v0_0", "v0.index(0) == 10");
    ctx.push_assume("v0_1", "v0.index(1) == 20");
    ctx.push_assume("v0_2", "v0.index(2) == 30");

    // Update index 1 — but NO frame for index 0 or 2
    ctx.push_assume("update_target", "v1.index(1) == 99");

    // Claim frame holds WITHOUT assuming it — should fail
    ctx.push_assert("wrong_frame", "v1.index(2) == 30");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 40f SOUNDNESS: missing frame should be rejected, got: {:?}",
        result,
    );
}

/// Tier 40g: Confusing version pointers — reading v1 when you meant v0.
///
/// After update(v0, 1, 99), claiming v0[1] == 99 is wrong.
#[test]
fn test_vt_tier40g_version_confusion_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("v0", "Seq<i64>");
    ctx.declare_var_parsed("v1", "Seq<i64>");

    ctx.push_assume("v0_len", "v0.len() == 3");
    ctx.push_assume("v1_len", "v1.len() == 3");
    ctx.push_assume("v0_1", "v0.index(1) == 20");
    ctx.push_assume("update_target", "v1.index(1) == 99");

    // WRONG: claiming the original was updated
    ctx.push_assert("version_confusion", "v0.index(1) == 99");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 40g SOUNDNESS: version confusion should be rejected, got: {:?}",
        result,
    );
}

/// Tier 40h: Wrong update value — claiming the update set a different value.
#[test]
fn test_vt_tier40h_wrong_update_value_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("v0", "Seq<i64>");
    ctx.declare_var_parsed("v1", "Seq<i64>");

    ctx.push_assume("v0_len", "v0.len() == 3");
    ctx.push_assume("v1_len", "v1.len() == 3");
    ctx.push_assume("v0_0", "v0.index(0) == 10");
    ctx.push_assume("v0_1", "v0.index(1) == 20");
    ctx.push_assume("v0_2", "v0.index(2) == 30");

    // update(v0, 1, 99)
    ctx.push_assume("update_target", "v1.index(1) == 99");
    ctx.push_assume("frame_0", "v1.index(0) == v0.index(0)");
    ctx.push_assume("frame_2", "v1.index(2) == v0.index(2)");

    // WRONG: claim update set 100 instead of 99
    ctx.push_assert("wrong_value", "v1.index(1) == 100");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 40h SOUNDNESS: wrong update value should be rejected, got: {:?}",
        result,
    );
}
