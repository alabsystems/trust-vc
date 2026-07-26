// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 41 - Rope concat/delete/insert VCs.
//!
//! VerifyThis 2024 included "The Rope Data Structure". The full challenge is
//! recursive/tree-shaped, but the proof-critical representation laws reduce to
//! sequence concatenation and split/delete equations over the represented
//! string. This tier exercises those laws through the stable verification
//! bridge.
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

fn assume_seq(ctx: &mut VerificationContext, name: &str, values: &[i64]) {
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

fn assume_lizard(ctx: &mut VerificationContext, name: &str) {
    assume_seq(ctx, name, &[108, 105, 122, 97, 114, 100]);
}

fn assume_lard(ctx: &mut VerificationContext, name: &str) {
    assume_seq(ctx, name, &[108, 97, 114, 100]);
}

fn assume_iz(ctx: &mut VerificationContext, name: &str) {
    assume_seq(ctx, name, &[105, 122]);
}

// ========================================================================
// GROUP A: Concat / repr laws
// ========================================================================

/// Tier 41a: concat repr is left ++ right.
#[test]
fn test_vt_tier41a_rope_concat_repr_law() {
    let mut ctx = VerificationContext::new();
    assume_seq(&mut ctx, "left", &[72, 101]);
    assume_seq(&mut ctx, "right", &[108, 108, 111]);

    ctx.push_assert(
        "concat_len_additive",
        "left.add(right).len() == left.len() + right.len()",
    );
    ctx.push_assert(
        "concat_preserves_left0",
        "left.add(right).index(0) == left.index(0)",
    );
    ctx.push_assert(
        "concat_preserves_left1",
        "left.add(right).index(1) == left.index(1)",
    );
    ctx.push_assert(
        "concat_boundary",
        "left.add(right).index(left.len()) == right.index(0)",
    );
    ctx.push_assert(
        "concat_preserves_right_last",
        "left.add(right).index(4) == right.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 41a: rope concat repr law should verify, got: {:?}",
        result,
    );
}

/// Tier 41b: splitting at the concat boundary recovers left and right lengths.
#[test]
fn test_vt_tier41b_rope_split_boundary_lengths() {
    let mut ctx = VerificationContext::new();
    assume_seq(&mut ctx, "left", &[72, 101]);
    assume_seq(&mut ctx, "right", &[108, 108, 111]);

    ctx.push_assert(
        "split_left_len",
        "left.add(right).take(2).len() == left.len()",
    );
    ctx.push_assert(
        "split_right_len",
        "left.add(right).skip(2).len() == right.len()",
    );
    ctx.push_assert(
        "split_left_elem0",
        "left.add(right).take(2).index(0) == left.index(0)",
    );
    ctx.push_assert(
        "split_right_head",
        "left.add(right).skip(2).index(0) == right.index(0)",
    );
    ctx.push_assert(
        "split_right_tail",
        "left.add(right).skip(2).index(2) == right.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 41b: rope split boundary lengths should verify, got: {:?}",
        result,
    );
}

/// Tier 41c: concat order matters.
#[test]
fn test_vt_tier41c_rope_concat_wrong_order_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq(&mut ctx, "left", &[72, 101]);
    assume_seq(&mut ctx, "right", &[108, 108, 111]);

    ctx.push_assert("wrong_head", "left.add(right).index(0) == right.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 41c SOUNDNESS: swapped rope concat order should be rejected, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Delete via split + concat
// ========================================================================

/// Tier 41d: delete("lizard", 1, 2) == "lard".
#[test]
fn test_vt_tier41d_rope_delete_lizard_to_lard() {
    let mut ctx = VerificationContext::new();
    assume_lizard(&mut ctx, "s");

    ctx.push_assert(
        "delete_len_complement",
        "s.take(1).add(s.skip(3)).len() + 2 == s.len()",
    );
    ctx.push_assert(
        "delete_prefix_matches_source",
        "s.take(1).add(s.skip(3)).index(0) == s.index(0)",
    );
    ctx.push_assert(
        "delete_suffix_start",
        "s.take(1).add(s.skip(3)).index(1) == s.index(3)",
    );
    ctx.push_assert(
        "delete_suffix_mid",
        "s.take(1).add(s.skip(3)).index(2) == s.index(4)",
    );
    ctx.push_assert(
        "delete_suffix_end",
        "s.take(1).add(s.skip(3)).index(3) == s.index(5)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 41d: rope delete example should verify, got: {:?}",
        result,
    );
}

/// Tier 41e: delete preserves prefix and suffix around the removed segment.
#[test]
fn test_vt_tier41e_rope_delete_preserves_prefix_and_suffix() {
    let mut ctx = VerificationContext::new();
    assume_lizard(&mut ctx, "s");

    ctx.push_assert(
        "prefix_kept",
        "s.take(1).add(s.skip(3)).index(0) == s.index(0)",
    );
    ctx.push_assert(
        "suffix_shift0",
        "s.take(1).add(s.skip(3)).index(1) == s.index(3)",
    );
    ctx.push_assert(
        "suffix_shift1",
        "s.take(1).add(s.skip(3)).index(2) == s.index(4)",
    );
    ctx.push_assert(
        "suffix_shift2",
        "s.take(1).add(s.skip(3)).index(3) == s.index(5)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 41e: rope delete prefix/suffix law should verify, got: {:?}",
        result,
    );
}

/// Tier 41f: delete must not retain the removed middle segment.
#[test]
fn test_vt_tier41f_rope_delete_removed_char_rejected() {
    let mut ctx = VerificationContext::new();
    assume_lizard(&mut ctx, "s");
    ctx.declare_var_parsed("deleted", "Seq<i64>");
    ctx.push_assume("deleted_len", "deleted.len() == 4");
    ctx.push_assume("deleted_0", "deleted.index(0) == s.index(0)");
    ctx.push_assume("deleted_1", "deleted.index(1) == s.index(3)");
    ctx.push_assume("deleted_2", "deleted.index(2) == s.index(4)");
    ctx.push_assume("deleted_3", "deleted.index(3) == s.index(5)");

    ctx.push_assert("removed_char_kept", "deleted.index(1) == 122");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 41f SOUNDNESS: deleted rope must not retain 'z', got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Insert extension
// ========================================================================

/// Tier 41g: insert("lard", 1, "iz") == "lizard".
#[test]
fn test_vt_tier41g_rope_insert_lard_to_lizard() {
    let mut ctx = VerificationContext::new();
    assume_lard(&mut ctx, "base");
    assume_iz(&mut ctx, "ins");

    ctx.push_assert(
        "insert_len_law",
        "base.take(1).add(ins).add(base.skip(1)).len() == base.len() + ins.len()",
    );
    ctx.push_assert(
        "insert_preserves_prefix",
        "base.take(1).add(ins).add(base.skip(1)).index(0) == base.index(0)",
    );
    ctx.push_assert(
        "insert_segment_0",
        "base.take(1).add(ins).add(base.skip(1)).index(1) == ins.index(0)",
    );
    ctx.push_assert(
        "insert_segment_1",
        "base.take(1).add(ins).add(base.skip(1)).index(2) == ins.index(1)",
    );
    ctx.push_assert(
        "insert_suffix_0",
        "base.take(1).add(ins).add(base.skip(1)).index(3) == base.index(1)",
    );
    ctx.push_assert(
        "insert_suffix_1",
        "base.take(1).add(ins).add(base.skip(1)).index(4) == base.index(2)",
    );
    ctx.push_assert(
        "insert_suffix_last",
        "base.take(1).add(ins).add(base.skip(1)).index(5) == base.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 41g: rope insert extension should verify, got: {:?}",
        result,
    );
}

/// Tier 41h: inserted segment order matters.
#[test]
fn test_vt_tier41h_rope_insert_wrong_order_rejected() {
    let mut ctx = VerificationContext::new();
    assume_lard(&mut ctx, "base");
    assume_iz(&mut ctx, "ins");
    ctx.declare_var_parsed("out", "Seq<i64>");
    ctx.push_assume("out_len", "out.len() == 6");
    ctx.push_assume("out_0", "out.index(0) == base.index(0)");
    ctx.push_assume("out_1", "out.index(1) == ins.index(0)");
    ctx.push_assume("out_2", "out.index(2) == ins.index(1)");
    ctx.push_assume("out_3", "out.index(3) == base.index(1)");
    ctx.push_assume("out_4", "out.index(4) == base.index(2)");
    ctx.push_assume("out_5", "out.index(5) == base.index(3)");

    ctx.push_assert("wrong_insert_order", "out.index(1) == 122");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 41h SOUNDNESS: rope insert with wrong order should be rejected, got: {:?}",
        result,
    );
}
