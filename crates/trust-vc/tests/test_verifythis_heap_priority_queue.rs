// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 34 — Binary Heap / Priority Queue VCs.
//!
//! Binary heaps are a recurring competition pattern: Dijkstra's algorithm,
//! work-stealing task trees (VerifyThis 2024), priority scheduling, and
//! heapsort all require heap property reasoning.
//!
//! We model a min-heap as `h: Seq<u64>` where the parent-child relationship
//! uses array indexing: parent(i) = (i-1)/2, left(i) = 2*i+1, right(i) = 2*i+2.
//! The heap property requires `h[parent(i)] <= h[i]` for all i > 0.
//!
//! Operations:
//!   - Insert (sift-up): add at end, bubble up to restore heap property
//!   - Extract-min (sift-down): swap root with last, shrink, bubble root down
//!   - Peek: return h[0] (the minimum element)
//!
//! KEY LESSON: Heap invariants are local — each parent-child pair can be checked
//! independently. The global "minimum at root" property follows from transitivity
//! of the local heap-order constraint.
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

fn assume_seq_u64_exprs(ctx: &mut VerificationContext, name: &str, exprs: &[&str]) {
    ctx.declare_var_parsed(name, "Seq<u64>");
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

// ========================================================================
// GROUP A: Heap property verification on concrete heaps
// ========================================================================

/// Tier 34a: 4-element min-heap h = [1, 3, 2, 7]. Relational assertions.
///
/// Tree shape:        1
///                   / \
///                  3   2
///                 /
///                7
///
/// Instead of echoing parent<=child from concrete values, assert derived
/// properties: root bounded by sum, grandparent-grandchild transitivity,
/// and sibling-sum bounds.
#[test]
fn test_vt_tier34a_min_heap_property_concrete() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "h", &[1, 3, 2, 7]);

    // Root * 4 <= sum (root is at most average, since it's the minimum)
    ctx.push_assert(
        "root_bounded_by_sum",
        "h.index(0) + h.index(0) + h.index(0) + h.index(0) <= h.index(0) + h.index(1) + h.index(2) + h.index(3)",
    );
    // Grandparent-grandchild: h[0] <= h[3] via transitive chain 0→1→3
    ctx.push_assert(
        "grandparent_grandchild_transitivity",
        "h.index(0) <= h.index(3)",
    );
    // Sibling-sum lower bound: both children >= root, so sum >= 2*root
    ctx.push_assert(
        "children_sum_exceeds_double_root",
        "h.index(1) + h.index(2) >= h.index(0) + h.index(0)",
    );
    // Non-root sum exceeds root-triple (stronger: 3+2+7=12 >= 1+1+1=3)
    ctx.push_assert(
        "non_root_sum_exceeds_root_triple",
        "h.index(1) + h.index(2) + h.index(3) >= h.index(0) + h.index(0) + h.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 34a: 4-element min-heap relational properties should verify, got: {:?}",
        result,
    );
}

/// Tier 34b: 7-element min-heap h = [1, 3, 2, 7, 5, 4, 6].
/// Verify cross-level relational properties on a complete binary tree.
#[test]
fn test_vt_tier34b_full_heap_all_parent_child() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "h", &[1, 3, 2, 7, 5, 4, 6]);

    // Root bounded by total: root * 7 <= sum
    ctx.push_assert(
        "root_bounded_by_total",
        "h.index(0) + h.index(0) + h.index(0) + h.index(0) + h.index(0) + h.index(0) + h.index(0) <= h.index(0) + h.index(1) + h.index(2) + h.index(3) + h.index(4) + h.index(5) + h.index(6)",
    );
    // Cross-level: all leaves >= root (4 transitive chains)
    ctx.push_assert("root_le_leaf3", "h.index(0) <= h.index(3)");
    ctx.push_assert("root_le_leaf4", "h.index(0) <= h.index(4)");
    ctx.push_assert("root_le_leaf5", "h.index(0) <= h.index(5)");
    ctx.push_assert("root_le_leaf6", "h.index(0) <= h.index(6)");
    // Level-2 sum exceeds level-1 sum (deeper levels hold larger elements)
    ctx.push_assert(
        "level2_sum_exceeds_level1_sum",
        "h.index(3) + h.index(4) + h.index(5) + h.index(6) >= h.index(1) + h.index(2) + h.index(1) + h.index(2)",
    );
    // Each subtree root bounds its subtree: h[1] <= min(h[3],h[4])
    // Express as: h[1]+h[1] <= h[3]+h[4]
    ctx.push_assert(
        "left_subtree_root_bounds_children",
        "h.index(1) + h.index(1) <= h.index(3) + h.index(4)",
    );
    ctx.push_assert(
        "right_subtree_root_bounds_children",
        "h.index(2) + h.index(2) <= h.index(5) + h.index(6)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 34b: 7-element complete min-heap relational properties should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Insert with sift-up (expression-based post-state)
// ========================================================================

/// Tier 34c: Insert value 0 into h = [1, 3, 2, 7] at position 4.
///
/// Sift-up path: pos 4 (parent 1), swap with h[1]=3; pos 1 (parent 0), swap
/// with h[0]=1. Post-state defined via expressions from pre-state, not
/// concrete values. Solver must expand expressions to verify properties.
#[test]
fn test_vt_tier34c_insert_sift_up_to_root() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("elem", "u64");
    ctx.push_assume("elem_val", "elem == 0");
    assume_seq_u64(&mut ctx, "h", &[1, 3, 2, 7]);

    // Post-state via sift-up expressions:
    //   elem sifts past h[1] and h[0] to root
    //   h[0] drops to pos 1, h[1] drops to pos 4
    //   h[2], h[3] untouched
    assume_seq_u64_exprs(
        &mut ctx,
        "h_new",
        &[
            "elem",       // sifted to root
            "h.index(0)", // old root pushed to pos 1
            "h.index(2)", // untouched
            "h.index(3)", // untouched
            "h.index(1)", // old pos-1 pushed to pos 4
        ],
    );

    // Heap property on post-state (solver expands expressions)
    ctx.push_assert("heap_01", "h_new.index(0) <= h_new.index(1)");
    ctx.push_assert("heap_02", "h_new.index(0) <= h_new.index(2)");
    ctx.push_assert("heap_13", "h_new.index(1) <= h_new.index(3)");
    ctx.push_assert("heap_14", "h_new.index(1) <= h_new.index(4)");
    // Element conservation: sum(h_new) == sum(h) + elem
    ctx.push_assert(
        "conservation",
        "h_new.index(0) + h_new.index(1) + h_new.index(2) + h_new.index(3) + h_new.index(4) == h.index(0) + h.index(1) + h.index(2) + h.index(3) + elem",
    );
    // Size grew by one
    ctx.push_assert("size_grew", "h_new.len() == h.len() + 1");
    // New root is the inserted element (smallest overall)
    ctx.push_assert("new_min", "h_new.index(0) <= h.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 34c: insert sift-up with expression post-state should verify, got: {:?}",
        result,
    );
}

/// Tier 34d: Insert value 4 into h = [1, 3, 2, 7] at position 4.
///
/// Sift-up: pos 4 (parent 1), h[1]=3 < 4, stop. Frame preserved via
/// expression-based definitions. Solver must verify frame + heap extension.
#[test]
fn test_vt_tier34d_insert_no_sift_frame_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("elem", "u64");
    ctx.push_assume("elem_val", "elem == 4");
    assume_seq_u64(&mut ctx, "h", &[1, 3, 2, 7]);

    // Post-state: no sift needed, original elements stay, elem appended
    assume_seq_u64_exprs(
        &mut ctx,
        "h_new",
        &[
            "h.index(0)", // frame
            "h.index(1)", // frame
            "h.index(2)", // frame
            "h.index(3)", // frame
            "elem",       // appended
        ],
    );

    // Frame: sum of original positions preserved
    ctx.push_assert(
        "frame_sum_preserved",
        "h_new.index(0) + h_new.index(1) + h_new.index(2) + h_new.index(3) == h.index(0) + h.index(1) + h.index(2) + h.index(3)",
    );
    // Frame: ordering gap between children preserved
    ctx.push_assert(
        "frame_child_gap_preserved",
        "h_new.index(1) + h_new.index(2) == h.index(1) + h.index(2)",
    );
    // Heap extends: parent of new element satisfies heap order
    ctx.push_assert("new_edge_heap", "h_new.index(1) <= h_new.index(4)");
    // Conservation
    ctx.push_assert(
        "conservation",
        "h_new.index(0) + h_new.index(1) + h_new.index(2) + h_new.index(3) + h_new.index(4) == h.index(0) + h.index(1) + h.index(2) + h.index(3) + elem",
    );
    // Root unchanged
    ctx.push_assert("root_preserved", "h_new.index(0) == h.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 34d: insert without sift-up should preserve frame, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Extract-min with sift-down (expression-based post-state)
// ========================================================================

/// Tier 34e: Extract-min from h = [1, 3, 2, 7, 5].
///
/// Step 1: extracted = h[0], swap root with last → [h[4], 3, 2, 7], size=4.
/// Step 2: sift-down h[4]=5: min child is h[2]=2 at pos 2. Swap.
///         → [h[2], h[1], h[4], h[3]]. Done (no children in bounds).
///
/// Post-state defined via expressions from pre-state.
#[test]
fn test_vt_tier34e_extract_min_sift_down() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("extracted", "u64");
    assume_seq_u64(&mut ctx, "h", &[1, 3, 2, 7, 5]);

    // Extracted value is old root
    ctx.push_assume("extracted_def", "extracted == h.index(0)");

    // Post-state via sift-down expressions:
    //   Swap root with last → temp[0] = h[4]
    //   Sift: h[4]=5 > min(h[1],h[2])=h[2]=2, swap with pos 2
    //   Result: [h[2], h[1], h[4], h[3]]
    assume_seq_u64_exprs(
        &mut ctx,
        "h_new",
        &[
            "h.index(2)", // min child promoted to root
            "h.index(1)", // untouched
            "h.index(4)", // last-element landed after sift
            "h.index(3)", // untouched
        ],
    );

    // Extracted was the minimum: smaller than new root
    ctx.push_assert("extracted_le_new_root", "extracted <= h_new.index(0)");
    // Heap property restored
    ctx.push_assert("heap_01", "h_new.index(0) <= h_new.index(1)");
    ctx.push_assert("heap_02", "h_new.index(0) <= h_new.index(2)");
    ctx.push_assert("heap_13", "h_new.index(1) <= h_new.index(3)");
    // Element conservation: extracted + sum(h_new) == sum(h)
    ctx.push_assert(
        "conservation",
        "extracted + h_new.index(0) + h_new.index(1) + h_new.index(2) + h_new.index(3) == h.index(0) + h.index(1) + h.index(2) + h.index(3) + h.index(4)",
    );
    // Size shrank
    ctx.push_assert("size_shrank", "h_new.len() + 1 == h.len()");
    // New root is minimum of remaining
    ctx.push_assert("new_root_le_all", "h_new.index(0) <= h_new.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 34e: extract-min sift-down with expression post-state should verify, got: {:?}",
        result,
    );
}

/// Tier 34f: Two consecutive extract-min operations.
///
/// Start: h = [1, 2, 3, 4, 5].
/// Extract 1 → h_mid = [2, 4, 3, 5].
/// Extract 2 → h_final = [3, 4, 5].
/// Verify monotonicity and conservation across both operations.
#[test]
fn test_vt_tier34f_two_extracts_monotone() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("ext1", "u64");
    ctx.declare_var_parsed("ext2", "u64");
    assume_seq_u64(&mut ctx, "h", &[1, 2, 3, 4, 5]);

    // First extract: ext1 = h[0]
    ctx.push_assume("ext1_def", "ext1 == h.index(0)");

    // After first extract + sift-down: [h[1], h[3], h[2], h[4]]
    assume_seq_u64_exprs(
        &mut ctx,
        "h_mid",
        &[
            "h.index(1)", // promoted to root
            "h.index(3)", // sifted from swap path
            "h.index(2)", // untouched
            "h.index(4)", // last element sifted down
        ],
    );

    // Second extract: ext2 = h_mid[0]
    ctx.push_assume("ext2_def", "ext2 == h_mid.index(0)");

    // After second extract + sift-down: [h_mid[2], h_mid[1], h_mid[3]]
    assume_seq_u64_exprs(
        &mut ctx,
        "h_final",
        &[
            "h_mid.index(2)", // min child promoted
            "h_mid.index(1)", // untouched
            "h_mid.index(3)", // last sifted down
        ],
    );

    // Monotonicity: extractions come out in sorted order
    ctx.push_assert("monotone", "ext1 <= ext2");
    ctx.push_assert("ext2_le_remaining", "ext2 <= h_final.index(0)");
    // Full conservation: ext1 + ext2 + sum(h_final) == sum(h)
    ctx.push_assert(
        "full_conservation",
        "ext1 + ext2 + h_final.index(0) + h_final.index(1) + h_final.index(2) == h.index(0) + h.index(1) + h.index(2) + h.index(3) + h.index(4)",
    );
    // Remaining heap is valid
    ctx.push_assert("final_heap_01", "h_final.index(0) <= h_final.index(1)");
    ctx.push_assert("final_heap_02", "h_final.index(0) <= h_final.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 34f: two consecutive extract-min with conservation should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Symbolic heap property reasoning
// ========================================================================

/// Tier 34g: If h[0] <= h[1] and h[0] <= h[2], and h[1] <= h[3],
/// then h[0] <= h[3] (transitivity through heap levels).
#[test]
fn test_vt_tier34g_heap_order_transitivity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("h", "Seq<u64>");

    ctx.push_assume("len", "h.len() == 4");
    ctx.push_assume("h0_bounded", "h.index(0) < 1000000");
    ctx.push_assume("h1_bounded", "h.index(1) < 1000000");
    ctx.push_assume("h3_bounded", "h.index(3) < 1000000");
    ctx.push_assume("heap_01", "h.index(0) <= h.index(1)");
    ctx.push_assume("heap_02", "h.index(0) <= h.index(2)");
    ctx.push_assume("heap_13", "h.index(1) <= h.index(3)");

    // Transitivity: root <= any descendant
    ctx.push_assert("root_le_leaf", "h.index(0) <= h.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 34g: heap order transitivity should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Soundness negatives
// ========================================================================

/// Tier 34h: Insert without sift-up violates heap property.
/// h = [1, 3, 2, 7], insert 0 at position 4 without sifting.
/// h_bad = [1, 3, 2, 7, 0]. Claim h_bad[1] <= h_bad[4] — FALSE (3 > 0).
#[test]
fn test_vt_tier34h_insert_no_sift_violates_heap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("elem", "u64");
    ctx.push_assume("elem_val", "elem == 0");
    assume_seq_u64(&mut ctx, "h", &[1, 3, 2, 7]);

    // WRONG: just append without sifting
    assume_seq_u64_exprs(
        &mut ctx,
        "h_bad",
        &[
            "h.index(0)",
            "h.index(1)",
            "h.index(2)",
            "h.index(3)",
            "elem", // appended at end, no sift-up
        ],
    );

    // Parent h_bad[1] should be <= child h_bad[4], but 3 > 0
    ctx.push_assert("broken_heap", "h_bad.index(1) <= h_bad.index(4)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 34h SOUNDNESS: insert without sift-up should violate heap, got: {:?}",
        result,
    );
}

/// Tier 34i: Claiming maximum is at root of a min-heap is wrong.
/// h = [1, 5, 3]. Assert h[0] >= h[1] — FALSE (1 < 5).
#[test]
fn test_vt_tier34i_max_at_root_of_min_heap_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_u64(&mut ctx, "h", &[1, 5, 3]);

    // WRONG: root is the minimum, not the maximum
    ctx.push_assert("wrong_max_at_root", "h.index(0) >= h.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 34i SOUNDNESS: max-at-root claim on min-heap should be rejected, got: {:?}",
        result,
    );
}
