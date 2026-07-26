// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 32 — Union-Find (Disjoint Sets) VCs.
//!
//! VerifyThis 2025 featured "Persistent Disjoint Sets" as a challenge problem.
//! Union-Find is the canonical disjoint-set data structure: a parent array
//! `p: Seq<u64>` where `p[x]` is the parent of element `x`, and roots satisfy
//! `p[root] == root`.
//!
//! Core operations:
//!   - `find(x)`: follow parent pointers to root
//!   - `union(x, y)`: link root of x to root of y
//!   - `path compression`: flatten paths during find
//!
//! We model the parent array as `Seq<u64>` (indices are elements, values are
//! parents). Without recursive function support, we unroll find to fixed depth
//! and use concrete traces for multi-step paths.
//!
//! KEY LESSON: Union-Find invariants are inductive over parent chains. The root
//! invariant (`p[r] == r`) is the base case; path properties (acyclicity,
//! reachability) require chain-length induction. Fixed-depth unrolling is the
//! competition-feasible approach for trust_vc.
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

// ========================================================================
// GROUP A: Root invariant and basic parent structure
// ========================================================================

/// Tier 32a: Root self-loop — initialized p[i] == i for all i.
#[test]
fn test_vt_tier32a_root_self_loop() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "Seq<u64>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("n_bounded", "n == 4");
    ctx.push_assume("len", "p.len() == n");
    // Initialized: every element is its own root
    ctx.push_assume("init0", "p.index(0) == 0");
    ctx.push_assume("init1", "p.index(1) == 1");
    ctx.push_assume("init2", "p.index(2) == 2");
    ctx.push_assume("init3", "p.index(3) == 3");

    // A second parent lookup is idempotent for every initialized root.
    ctx.push_assert("root_closure_0", "p.index(p.index(0)) == 0");
    ctx.push_assert("root_closure_1", "p.index(p.index(1)) == 1");
    ctx.push_assert("root_closure_2", "p.index(p.index(2)) == 2");
    ctx.push_assert("root_closure_3", "p.index(p.index(3)) == 3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 32a: initialized root self-loops should verify, got: {:?}",
        result,
    );
}

/// Tier 32b: Symbolic root — if p[r] == r then find(r) == r.
#[test]
fn test_vt_tier32b_symbolic_root_find() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "Seq<u64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("r", "u64");

    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("len", "p.len() == n");
    ctx.push_assume("r_in_bounds", "r < n");
    ctx.push_assume("r_is_root", "p.index(r) == r");

    // A root stays fixed under one more parent lookup and remains in-bounds.
    ctx.push_assert("find_root_closure", "p.index(p.index(r)) == r");
    ctx.push_assert("find_root_in_bounds", "p.index(r) < p.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 32b: symbolic root find should verify, got: {:?}",
        result,
    );
}

/// Tier 32c: Non-root parent structure after union(0, 1).
#[test]
fn test_vt_tier32c_non_root_points_elsewhere() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "Seq<u64>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("n_is_4", "n == 4");
    ctx.push_assume("len", "p.len() == n");
    // After union(0, 1): p[0] = 1, everything else unchanged
    ctx.push_assume("p0", "p.index(0) == 1");
    ctx.push_assume("p1", "p.index(1) == 1");
    ctx.push_assume("p2", "p.index(2) == 2");
    ctx.push_assume("p3", "p.index(3) == 3");

    // 0 is NOT a root
    ctx.push_assert("zero_not_root", "p.index(0) != 0");
    // 0's parent is a root
    ctx.push_assert("zero_parent_is_root", "p.index(p.index(0)) == p.index(0)");
    // 0 and 1 still collapse to the same root representative.
    ctx.push_assert(
        "zero_and_one_share_root",
        "p.index(p.index(0)) == p.index(p.index(1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 32c: non-root parent structure should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Find operation (depth-bounded unrolling)
// ========================================================================

/// Tier 32d: Depth-1 find — p = [0, 1, 0, 3], find(2) = 0.
#[test]
fn test_vt_tier32d_depth_one_find() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "Seq<u64>");
    ctx.declare_var_parsed("x", "u64");
    ctx.declare_var_parsed("root", "u64");

    ctx.push_assume("len", "p.len() == 4");
    ctx.push_assume("p0", "p.index(0) == 0");
    ctx.push_assume("p1", "p.index(1) == 1");
    ctx.push_assume("p2", "p.index(2) == 0");
    ctx.push_assume("p3", "p.index(3) == 3");
    ctx.push_assume("x_is_2", "x == 2");
    ctx.push_assume("root_def", "root == p.index(x)");

    // One step reaches the root
    ctx.push_assert("root_is_zero", "root == 0");
    ctx.push_assert("root_is_root", "p.index(root) == root");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 32d: depth-1 find should verify, got: {:?}",
        result,
    );
}

/// Tier 32e: Depth-2 find — chain 3 → 2 → 0, p = [0, 1, 0, 2].
#[test]
fn test_vt_tier32e_depth_two_find() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "Seq<u64>");
    ctx.declare_var_parsed("x", "u64");
    ctx.declare_var_parsed("step1", "u64");
    ctx.declare_var_parsed("step2", "u64");

    ctx.push_assume("len", "p.len() == 4");
    ctx.push_assume("p0", "p.index(0) == 0");
    ctx.push_assume("p1", "p.index(1) == 1");
    ctx.push_assume("p2", "p.index(2) == 0");
    ctx.push_assume("p3", "p.index(3) == 2");
    ctx.push_assume("x_is_3", "x == 3");
    ctx.push_assume("step1_def", "step1 == p.index(x)");
    ctx.push_assume("step2_def", "step2 == p.index(step1)");

    // Two steps reach the root
    ctx.push_assert("step1_is_2", "step1 == 2");
    ctx.push_assert("step2_is_0", "step2 == 0");
    ctx.push_assert("step2_is_root", "p.index(step2) == step2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 32e: depth-2 find should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Union operation — set p[find(x)] = find(y)
// ========================================================================

/// Tier 32f: Union merges {0,2} and {1,3} via p[0] = 1.
#[test]
fn test_vt_tier32f_union_merges_components() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "Seq<u64>");
    ctx.declare_var_parsed("p_new", "Seq<u64>");
    ctx.declare_var_parsed("root_x", "u64");
    ctx.declare_var_parsed("root_y", "u64");

    ctx.push_assume("len", "p.len() == 4");
    ctx.push_assume("p0", "p.index(0) == 0");
    ctx.push_assume("p1", "p.index(1) == 1");
    ctx.push_assume("p2", "p.index(2) == 0");
    ctx.push_assume("p3", "p.index(3) == 1");

    // find(2) = 0, find(3) = 1
    ctx.push_assume("root_x_def", "root_x == p.index(2)");
    ctx.push_assume("root_y_def", "root_y == p.index(3)");
    ctx.push_assume("root_x_is_root", "p.index(root_x) == root_x");
    ctx.push_assume("root_y_is_root", "p.index(root_y) == root_y");

    // Union: p_new[root_x] = root_y, everything else unchanged
    ctx.push_assume("len_new", "p_new.len() == 4");
    ctx.push_assume("union_link", "p_new.index(root_x) == root_y");
    // Frame: non-root_x elements unchanged
    ctx.push_assume("frame_1", "p_new.index(1) == p.index(1)");
    ctx.push_assume("frame_2", "p_new.index(2) == p.index(2)");
    ctx.push_assume("frame_3", "p_new.index(3) == p.index(3)");

    // After union: root_x no longer a root, root_y still a root
    ctx.push_assert("root_x_linked", "p_new.index(0) == 1");
    ctx.push_assert("root_y_unchanged", "p_new.index(1) == 1");
    // Element 2 still points to 0, which now points to 1
    ctx.push_assert("elem2_parent", "p_new.index(2) == 0");
    ctx.push_assert("elem2_grandparent", "p_new.index(p_new.index(2)) == 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 32f: union merging two components should verify, got: {:?}",
        result,
    );
}

/// Tier 32g: Symbolic union frame — e != root_x implies p_new[e] == p[e].
#[test]
fn test_vt_tier32g_union_frame_condition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "Seq<u64>");
    ctx.declare_var_parsed("p_new", "Seq<u64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("root_x", "u64");
    ctx.declare_var_parsed("root_y", "u64");
    ctx.declare_var_parsed("e", "u64");

    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("len", "p.len() == n");
    ctx.push_assume("len_new", "p_new.len() == n");
    ctx.push_assume("root_x_bounds", "root_x < n");
    ctx.push_assume("root_y_bounds", "root_y < n");
    ctx.push_assume("e_bounds", "e < n");

    // Union: p_new = p with p_new[root_x] = root_y
    ctx.push_assume("union_link", "p_new.index(root_x) == root_y");
    ctx.push_assume(
        "union_frame",
        "forall(|k: u64| !(k < n && k != root_x) || p_new.index(k) == p.index(k))",
    );

    // For any e != root_x, parent is unchanged
    ctx.push_assume("e_not_root_x", "e != root_x");
    ctx.push_assert("frame_preserved", "p_new.index(e) == p.index(e)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 32g: union frame condition should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Path compression — find(x) sets p[x] = root directly
// ========================================================================

/// Tier 32h: Path compression flattens chain 3 → 2 → 0 to 3 → 0.
#[test]
fn test_vt_tier32h_path_compression() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "Seq<u64>");
    ctx.declare_var_parsed("p_new", "Seq<u64>");
    ctx.declare_var_parsed("root", "u64");

    ctx.push_assume("len", "p.len() == 4");
    ctx.push_assume("len_new", "p_new.len() == 4");
    // Before: 3 → 2 → 0 (root)
    ctx.push_assume("p0", "p.index(0) == 0");
    ctx.push_assume("p1", "p.index(1) == 1");
    ctx.push_assume("p2", "p.index(2) == 0");
    ctx.push_assume("p3", "p.index(3) == 2");
    ctx.push_assume("root_is_0", "root == 0");

    // After path compression: 3 → 0 directly
    ctx.push_assume("comp3", "p_new.index(3) == root");
    ctx.push_assume("comp2", "p_new.index(2) == root");
    ctx.push_assume("comp0", "p_new.index(0) == p.index(0)");
    ctx.push_assume("comp1", "p_new.index(1) == p.index(1)");

    // Root unchanged
    ctx.push_assert("root_preserved", "p_new.index(0) == 0");
    // 3 now points directly to root
    ctx.push_assert("three_direct", "p_new.index(3) == 0");
    // Component membership preserved: find(3) still reaches 0
    ctx.push_assert("find3_root", "p_new.index(p_new.index(3)) == 0");
    // Depth reduced: the compressed nodes now point to the same root directly.
    ctx.push_assert(
        "compressed_nodes_share_root",
        "p_new.index(3) == p_new.index(2)",
    );
    ctx.push_assert("root_self_loop", "p_new.index(root) == root");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 32h: path compression should verify, got: {:?}",
        result,
    );
}

/// Tier 32i: Compression preserves same-component (2 and 3 both reach 0).
#[test]
fn test_vt_tier32i_compression_preserves_component() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "Seq<u64>");
    ctx.declare_var_parsed("p_new", "Seq<u64>");

    ctx.push_assume("len", "p.len() == 4");
    ctx.push_assume("len_new", "p_new.len() == 4");
    // Before
    ctx.push_assume("p0", "p.index(0) == 0");
    ctx.push_assume("p1", "p.index(1) == 1");
    ctx.push_assume("p2", "p.index(2) == 0");
    ctx.push_assume("p3", "p.index(3) == 2");

    // After compression of 3: only 3's parent changes
    ctx.push_assume("comp3", "p_new.index(3) == 0");
    ctx.push_assume("unchanged0", "p_new.index(0) == p.index(0)");
    ctx.push_assume("unchanged1", "p_new.index(1) == p.index(1)");
    ctx.push_assume("unchanged2", "p_new.index(2) == p.index(2)");

    // Both 2 and 3 reach root 0 in p_new
    // find(2): p_new[2] = 0, p_new[0] = 0 ✓
    ctx.push_assert("find2_root", "p_new.index(p_new.index(2)) == 0");
    // find(3): p_new[3] = 0, p_new[0] = 0 ✓
    ctx.push_assert("find3_root", "p_new.index(p_new.index(3)) == 0");
    // Same root
    ctx.push_assert(
        "same_component",
        "p_new.index(p_new.index(2)) == p_new.index(p_new.index(3))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 32i: compression preserves same-component should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Concrete multi-operation trace
// ========================================================================

/// Tier 32j: 3 unions then find — all 4 elements reach root 3.
#[test]
fn test_vt_tier32j_multi_operation_trace() {
    let mut ctx = VerificationContext::new();
    // State after all three unions
    ctx.declare_var_parsed("p", "Seq<u64>");

    ctx.push_assume("len", "p.len() == 4");
    ctx.push_assume("p0", "p.index(0) == 1");
    ctx.push_assume("p1", "p.index(1) == 3");
    ctx.push_assume("p2", "p.index(2) == 3");
    ctx.push_assume("p3", "p.index(3) == 3");

    // All elements reach root 3 after enough parent traversals.
    ctx.push_assert("find3_root_closure", "p.index(p.index(3)) == 3");
    ctx.push_assert("find2_root", "p.index(p.index(2)) == 3");
    ctx.push_assert("find1_root", "p.index(p.index(1)) == 3");
    ctx.push_assert("find0_step2", "p.index(p.index(0)) == 3");
    ctx.push_assert("find0_root", "p.index(p.index(p.index(0))) == 3");

    // Single connected component: all find to 3
    ctx.push_assert(
        "all_same_root",
        "p.index(p.index(0)) == p.index(p.index(2))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 32j: multi-operation trace should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP F: Soundness negatives
// ========================================================================

/// Tier 32k: Wrong find — claiming find(3) == 2 when root is 0.
#[test]
fn test_vt_tier32k_wrong_find_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "Seq<u64>");
    ctx.declare_var_parsed("step1", "u64");
    ctx.declare_var_parsed("step2", "u64");

    ctx.push_assume("len", "p.len() == 4");
    ctx.push_assume("p0", "p.index(0) == 0");
    ctx.push_assume("p1", "p.index(1) == 1");
    ctx.push_assume("p2", "p.index(2) == 0");
    ctx.push_assume("p3", "p.index(3) == 2");
    ctx.push_assume("step1_def", "step1 == p.index(3)");
    ctx.push_assume("step2_def", "step2 == p.index(step1)");

    // WRONG: find(3) should be 0, not 2
    // p[3] = 2 is just the first step; the second step reaches root 0.
    ctx.push_assert("wrong_find", "step2 == 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 32k SOUNDNESS: wrong find claiming non-root should be rejected, got: {:?}",
        result,
    );
}

/// Tier 32l: Linking non-root 2 instead of root 0 orphans element 0.
#[test]
fn test_vt_tier32l_union_on_non_root_breaks_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "Seq<u64>");
    ctx.declare_var_parsed("p_bad", "Seq<u64>");
    ctx.declare_var_parsed("root0", "u64");
    ctx.declare_var_parsed("step1", "u64");
    ctx.declare_var_parsed("step2", "u64");
    ctx.declare_var_parsed("root3", "u64");

    ctx.push_assume("len", "p.len() == 4");
    ctx.push_assume("len_bad", "p_bad.len() == 4");
    // Before: 3 → 2 → 0 (root), 1 is separate root
    ctx.push_assume("p0", "p.index(0) == 0");
    ctx.push_assume("p1", "p.index(1) == 1");
    ctx.push_assume("p2", "p.index(2) == 0");
    ctx.push_assume("p3", "p.index(3) == 2");

    // BAD union: link non-root 2 to 1 (instead of linking root 0 to 1)
    ctx.push_assume("bad_p0", "p_bad.index(0) == 0");
    ctx.push_assume("bad_p1", "p_bad.index(1) == 1");
    ctx.push_assume("bad_p2", "p_bad.index(2) == 1");
    ctx.push_assume("bad_p3", "p_bad.index(3) == 2");
    ctx.push_assume("root0_def", "root0 == p_bad.index(0)");
    ctx.push_assume("step1_def", "step1 == p_bad.index(3)");
    ctx.push_assume("step2_def", "step2 == p_bad.index(step1)");
    ctx.push_assume("root3_def", "root3 == p_bad.index(step2)");

    // WRONG: 0 and 3 are in the same component (they're not anymore)
    // find(0) = 0 (root), find(3) = 3 → 2 → 1 (root 1)
    // So 0 and 3 have different roots
    ctx.push_assert("wrong_same_component", "root0 == root3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 32l SOUNDNESS: union on non-root should break same-component, got: {:?}",
        result,
    );
}
