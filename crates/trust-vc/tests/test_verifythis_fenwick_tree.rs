// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 76 - Fenwick Tree / Binary Indexed Tree VCs.
//!
//! Fenwick trees support point updates and prefix/range sum queries in
//! logarithmic time by storing lowbit-sized suffix sums of prefixes.
//!
//! Core proof obligations:
//!   1. Each tree entry stores the sum of the interval `[i-lowbit(i)+1, i]`.
//!   2. Prefix queries decompose into disjoint lowbit blocks while descending.
//!   3. Range sums subtract adjacent prefix queries.
//!   4. A point update changes exactly the queried index's ancestors.
//!   5. Negatives: updating a non-ancestor, using the wrong query path, or
//!      subtracting the wrong prefix are unsound.
//!
//! Example values (Fenwick positions 1..5):
//!   values = [3, 1, 4, 0, 2]
//!   tree   = [3, 4, 4, 8, 2]
//!   prefix = [3, 4, 8, 8, 10]
//!
//! Prefix query traces:
//!   prefix(3) = tree[3] + tree[2] = 4 + 4 = 8
//!   prefix(5) = tree[5] + tree[4] = 2 + 8 = 10
//!
//! Point-update trace: add `delta = 2` at position `3`
//!   updated_values = [3, 1, 6, 0, 2]
//!   updated_tree   = [3, 4, 6, 10, 2]
//!   updated_prefix = [3, 4, 10, 10, 12]
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

fn assume_fenwick_example(ctx: &mut VerificationContext) {
    assume_seq_u64(ctx, "values", &[3, 1, 4, 0, 2]);
    assume_seq_u64(ctx, "tree", &[3, 4, 4, 8, 2]);
    assume_seq_u64(ctx, "prefix", &[3, 4, 8, 8, 10]);
}

fn assume_fenwick_update(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("update_pos", "u64");
    ctx.declare_var_parsed("delta", "u64");
    ctx.push_assume("update_pos_3", "update_pos == 3");
    ctx.push_assume("delta_2", "delta == 2");
    assume_seq_u64(ctx, "updated_values", &[3, 1, 6, 0, 2]);
    assume_seq_u64(ctx, "updated_tree", &[3, 4, 6, 10, 2]);
    assume_seq_u64(ctx, "updated_prefix", &[3, 4, 10, 10, 12]);
}

// ========================================================================
// GROUP A: Lowbit blocks and prefix table
// ========================================================================

/// Tier 76a: each Fenwick node stores the sum of its lowbit-sized suffix block.
#[test]
fn test_vt_tier76a_tree_entries_match_lowbit_suffix_blocks() {
    let mut ctx = VerificationContext::new();
    assume_fenwick_example(&mut ctx);

    ctx.push_assert("tree_1_block", "tree.index(0) == values.index(0)");
    ctx.push_assert(
        "tree_2_block",
        "tree.index(1) == values.index(0) + values.index(1)",
    );
    ctx.push_assert("tree_3_block", "tree.index(2) == values.index(2)");
    ctx.push_assert(
        "tree_4_block",
        "tree.index(3) == values.index(0) + values.index(1) + values.index(2) + values.index(3)",
    );
    ctx.push_assert("tree_5_block", "tree.index(4) == values.index(4)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 76a: Fenwick lowbit blocks should verify, got: {:?}",
        result,
    );
}

/// Tier 76a: the recorded prefix sums agree with the lowbit block decomposition.
#[test]
fn test_vt_tier76a_prefix_table_agrees_with_tree_blocks() {
    let mut ctx = VerificationContext::new();
    assume_fenwick_example(&mut ctx);

    ctx.push_assert("prefix_1", "prefix.index(0) == tree.index(0)");
    ctx.push_assert("prefix_2", "prefix.index(1) == tree.index(1)");
    ctx.push_assert(
        "prefix_3",
        "prefix.index(2) == tree.index(2) + tree.index(1)",
    );
    ctx.push_assert("prefix_4", "prefix.index(3) == tree.index(3)");
    ctx.push_assert(
        "prefix_5",
        "prefix.index(4) == tree.index(4) + tree.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 76a: prefix table should match Fenwick blocks, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Prefix and range query decomposition
// ========================================================================

/// Tier 76b: prefix(3) descends through nodes 3 and 2, covering disjoint blocks.
#[test]
fn test_vt_tier76b_prefix_three_uses_nodes_three_and_two() {
    let mut ctx = VerificationContext::new();
    assume_fenwick_example(&mut ctx);

    ctx.push_assert(
        "prefix_3_from_tree_path",
        "prefix.index(2) == tree.index(2) + tree.index(1)",
    );
    ctx.push_assert(
        "tree_2_covers_first_two_values",
        "tree.index(1) == values.index(0) + values.index(1)",
    );
    ctx.push_assert(
        "prefix_3_closed_form",
        "prefix.index(2) == values.index(0) + values.index(1) + values.index(2)",
    );
    ctx.push_assert(
        "remove_last_node_recovers_prefix_2",
        "prefix.index(2) - tree.index(2) == prefix.index(1)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 76b: prefix(3) query path should verify, got: {:?}",
        result,
    );
}

/// Tier 76b: prefix(5) uses the singleton suffix node 5 and the large block at node 4.
#[test]
fn test_vt_tier76b_prefix_five_uses_suffix_and_large_block() {
    let mut ctx = VerificationContext::new();
    assume_fenwick_example(&mut ctx);

    ctx.push_assert(
        "prefix_5_from_tree_path",
        "prefix.index(4) == tree.index(4) + tree.index(3)",
    );
    ctx.push_assert("tree_4_is_prefix_4", "tree.index(3) == prefix.index(3)");
    ctx.push_assert(
        "drop_suffix_recovers_prefix_4",
        "prefix.index(4) - tree.index(4) == prefix.index(3)",
    );
    ctx.push_assert(
        "prefix_5_closed_form",
        "prefix.index(4) == values.index(0) + values.index(1) + values.index(2) + values.index(3) + values.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 76b: prefix(5) query path should verify, got: {:?}",
        result,
    );
}

/// Tier 76b: range sum on positions 2..5 subtracts prefix(1) from prefix(5).
#[test]
fn test_vt_tier76b_range_two_through_five_is_prefix_difference() {
    let mut ctx = VerificationContext::new();
    assume_fenwick_example(&mut ctx);

    ctx.push_assert(
        "range_2_5",
        "prefix.index(4) - prefix.index(0) == values.index(1) + values.index(2) + values.index(3) + values.index(4)",
    );
    ctx.push_assert(
        "range_2_5_equals_suffix_plus_middle",
        "prefix.index(4) - prefix.index(0) == tree.index(4) + values.index(1) + values.index(2) + values.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 76b: range query via prefix subtraction should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Point update propagation
// ========================================================================

/// Tier 76c: updating position 3 by +2 changes exactly Fenwick nodes 3 and 4.
#[test]
fn test_vt_tier76c_update_changes_exact_ancestors() {
    let mut ctx = VerificationContext::new();
    assume_fenwick_example(&mut ctx);
    assume_fenwick_update(&mut ctx);

    ctx.push_assert(
        "updated_value_at_pos",
        "updated_values.index(2) == values.index(2) + delta",
    );
    ctx.push_assert(
        "tree_node_3_gains_delta",
        "updated_tree.index(2) == tree.index(2) + delta",
    );
    ctx.push_assert(
        "tree_node_4_gains_delta",
        "updated_tree.index(3) == tree.index(3) + delta",
    );
    ctx.push_assert(
        "tree_node_1_unchanged",
        "updated_tree.index(0) == tree.index(0)",
    );
    ctx.push_assert(
        "tree_node_2_unchanged",
        "updated_tree.index(1) == tree.index(1)",
    );
    ctx.push_assert(
        "tree_node_5_unchanged",
        "updated_tree.index(4) == tree.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 76c: point update should affect exactly its Fenwick ancestors, got: {:?}",
        result,
    );
}

/// Tier 76c: prefix sums before position 3 stay fixed, while later prefixes gain delta.
#[test]
fn test_vt_tier76c_late_prefixes_absorb_delta() {
    let mut ctx = VerificationContext::new();
    assume_fenwick_example(&mut ctx);
    assume_fenwick_update(&mut ctx);

    ctx.push_assert(
        "prefix_before_update_fixed",
        "updated_prefix.index(1) == prefix.index(1)",
    );
    ctx.push_assert(
        "prefix_at_update_gains_delta",
        "updated_prefix.index(2) == prefix.index(2) + delta",
    );
    ctx.push_assert(
        "prefix_after_update_gains_delta",
        "updated_prefix.index(3) == prefix.index(3) + delta",
    );
    ctx.push_assert(
        "final_prefix_gains_delta",
        "updated_prefix.index(4) == prefix.index(4) + delta",
    );
    ctx.push_assert(
        "updated_total_matches_updated_values",
        "updated_prefix.index(4) == updated_values.index(0) + updated_values.index(1) + updated_values.index(2) + updated_values.index(3) + updated_values.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 76c: later prefixes should absorb the point-update delta, got: {:?}",
        result,
    );
}

/// Tier 76c: the updated range sum on positions 3..4 still comes from a prefix difference.
#[test]
fn test_vt_tier76c_updated_range_three_through_four_uses_prefix_difference() {
    let mut ctx = VerificationContext::new();
    assume_fenwick_example(&mut ctx);
    assume_fenwick_update(&mut ctx);

    ctx.push_assert(
        "range_3_4_after_update",
        "updated_prefix.index(3) - updated_prefix.index(1) == updated_values.index(2) + updated_values.index(3)",
    );
    ctx.push_assert(
        "only_third_value_changed",
        "updated_values.index(3) == values.index(3)",
    );
    ctx.push_assert(
        "updated_range_exceeds_old_range_by_delta",
        "updated_prefix.index(3) - updated_prefix.index(1) == (prefix.index(3) - prefix.index(1)) + delta",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 76c: updated range query should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Negative soundness checks
// ========================================================================

/// Tier 76d NEGATIVE: updating position 3 does not affect node 5, which is not an ancestor.
#[test]
fn test_vt_tier76d_nonancestor_node_update_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_fenwick_example(&mut ctx);
    assume_fenwick_update(&mut ctx);

    ctx.push_assert(
        "wrong_node_5_update",
        "updated_tree.index(4) == tree.index(4) + delta",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 76d SOUNDNESS: non-ancestor Fenwick node should stay unchanged, got: {:?}",
        result,
    );
}

/// Tier 76d NEGATIVE: prefix(5) cannot be reconstructed from nodes 5 and 3.
#[test]
fn test_vt_tier76d_wrong_prefix_path_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_fenwick_example(&mut ctx);

    ctx.push_assert(
        "wrong_prefix_path",
        "prefix.index(4) == tree.index(4) + tree.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 76d SOUNDNESS: wrong prefix-query path should be rejected, got: {:?}",
        result,
    );
}

/// Tier 76d NEGATIVE: subtracting prefix(2) instead of prefix(1) undercounts range 2..5.
#[test]
fn test_vt_tier76d_off_by_one_range_subtraction_is_unsound() {
    let mut ctx = VerificationContext::new();
    assume_fenwick_example(&mut ctx);

    ctx.push_assert(
        "wrong_range_difference",
        "prefix.index(4) - prefix.index(1) == values.index(1) + values.index(2) + values.index(3) + values.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 76d SOUNDNESS: off-by-one range subtraction should be rejected, got: {:?}",
        result,
    );
}
