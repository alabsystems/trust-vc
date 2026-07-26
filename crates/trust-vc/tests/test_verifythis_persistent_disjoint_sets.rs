// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 48 — Persistent Disjoint Sets VCs.
//!
//! VerifyThis 2025 featured "Persistent Disjoint Sets" as a challenge problem.
//! This combines two concepts already covered separately:
//!   - Union-Find (Tier 32): parent arrays, find, union, path compression
//!   - Persistent Arrays (Tier 40): functional update, version independence
//!
//! The key idea: each union or path-compression operation produces a **new**
//! version of the parent array while preserving all previous versions. This
//! enables rollback, branching histories, and concurrent reads on old snapshots.
//!
//! Core properties unique to persistent disjoint sets:
//!   1. Persistent union: `union(v_old, x, y) -> v_new` creates a new array
//!      version where `v_new[find(x)] = find(y)`, while `v_old` is unchanged
//!   2. Persistent find: `find` on `v_old` still returns the same root
//!      even after creating `v_new` from `v_old`
//!   3. Rollback: branching from any historical version produces valid results
//!   4. Persistent path compression: `find_compress(v_old, x) -> (root, v_new)`
//!      creates a flattened version while preserving the original chain
//!
//! Encoding: parent arrays as `Seq<u64>`, each version is a distinct symbolic
//! sequence. Frame conditions tie version transitions together.
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

/// Set up a 4-element parent array version with concrete values.
fn assume_parent_version(ctx: &mut VerificationContext, name: &str, parents: &[u64]) {
    let len_cond = format!("{name}.len() == {}", parents.len());
    ctx.declare_var_parsed(name, "Seq<u64>");
    ctx.push_assume(&format!("{name}_len"), &len_cond);
    for (idx, &parent) in parents.iter().enumerate() {
        let cond = format!("{name}.index({idx}) == {parent}");
        ctx.push_assume(&format!("{name}_{idx}"), &cond);
    }
}

// ========================================================================
// GROUP A: Persistent union — version isolation
// ========================================================================

/// Tier 48a: persistent union creates v1 while v0 stays unchanged.
///
/// v0 = [0, 1, 2, 3] (4 singletons)
/// union(v0, 0, 1) -> v1 = [1, 1, 2, 3]
/// v0 is still [0, 1, 2, 3].
#[test]
fn test_vt_tier48a_persistent_union_version_isolation() {
    let mut ctx = VerificationContext::new();
    // v0: 4 singletons
    assume_parent_version(&mut ctx, "v0", &[0, 1, 2, 3]);
    // v1: after union(0, 1) — root of 0 (which is 0) points to root of 1 (which is 1)
    assume_parent_version(&mut ctx, "v1", &[1, 1, 2, 3]);

    // The new version links 0's old root to 1's root while preserving unrelated nodes.
    ctx.push_assert(
        "v1_old_root_points_to_new_root",
        "v1.index(v0.index(0)) == v0.index(1)",
    );
    ctx.push_assert(
        "v1_new_root_is_stable",
        "v1.index(v1.index(0)) == v0.index(1)",
    );
    ctx.push_assert("v1_preserves_unrelated_2", "v1.index(2) == v0.index(2)");
    ctx.push_assert("v1_preserves_unrelated_3", "v1.index(3) == v0.index(3)");
    ctx.push_assert(
        "v0_and_v1_differ_at_the_updated_link",
        "v0.index(0) != v1.index(0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 48a: persistent union version isolation should verify, got: {:?}",
        result,
    );
}

/// Tier 48b: find on old version returns old root, not the union'd root.
///
/// v0 = [0, 1, 0, 3], v1 = union(v0, 2, 3) = [3, 1, 0, 3]
/// find(2, v0) = 0, find(2, v1) = 3 (since v1[0] = 3)
#[test]
fn test_vt_tier48b_find_on_old_version_returns_old_root() {
    let mut ctx = VerificationContext::new();
    // v0: {0,2} and {1} and {3} — element 2 points to 0
    assume_parent_version(&mut ctx, "v0", &[0, 1, 0, 3]);
    // v1: union(root_of_2=0, root_of_3=3) => v1[0] = 3
    assume_parent_version(&mut ctx, "v1", &[3, 1, 0, 3]);

    // The old version still finds 2's original representative, while the new version
    // reaches the newly attached root 3 through an extra step.
    ctx.push_assert(
        "find2_v0_root_matches_old_repr",
        "v0.index(v0.index(2)) == v0.index(0)",
    );
    ctx.push_assert(
        "find2_v1_root_matches_new_repr",
        "v1.index(v1.index(v1.index(2))) == v1.index(v1.index(2))",
    );
    ctx.push_assert(
        "find2_v1_root_is_component_3",
        "v1.index(v1.index(2)) == v1.index(3)",
    );
    ctx.push_assert(
        "roots_differ_across_versions",
        "v0.index(v0.index(2)) != v1.index(v1.index(2))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 48b: find on old version should return old root, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Persistent path compression
// ========================================================================

/// Tier 48c: persistent path compression creates a flattened version
/// while preserving the original chain.
///
/// v0 = [0, 1, 0, 2] (chain: 3 → 2 → 0)
/// find_compress(v0, 3) -> (root=0, v1=[0, 1, 0, 0])
/// v0 still has the original chain 3 → 2 → 0.
#[test]
fn test_vt_tier48c_persistent_path_compression() {
    let mut ctx = VerificationContext::new();
    // v0: chain 3 → 2 → 0 (root)
    assume_parent_version(&mut ctx, "v0", &[0, 1, 0, 2]);
    // v1: after compressing find(3), element 3 points directly to root 0
    assume_parent_version(&mut ctx, "v1", &[0, 1, 0, 0]);

    // Compression should redirect 3 to the old root without changing the root itself.
    ctx.push_assert(
        "compressed_pointer_targets_old_root",
        "v1.index(3) == v0.index(v0.index(3))",
    );
    ctx.push_assert("compression_shortens_path", "v1.index(3) != v0.index(3)");
    ctx.push_assert(
        "intermediate_parent_is_preserved",
        "v1.index(2) == v0.index(2)",
    );
    ctx.push_assert(
        "same_root_both_versions",
        "v0.index(v0.index(v0.index(3))) == v1.index(v1.index(3))",
    );
    ctx.push_assert(
        "compressed_root_is_stable",
        "v1.index(v1.index(3)) == v1.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 48c: persistent path compression should verify, got: {:?}",
        result,
    );
}

/// Tier 48d: compression of one path does not affect another element's
/// find result on the original version.
///
/// v0 = [0, 0, 1, 2], chains: 3→2→1→0, also 2→1→0
/// After compressing find(3): v1 = [0, 0, 0, 0]
/// But find(2, v0) still goes through the original chain 2→1→0.
#[test]
fn test_vt_tier48d_compression_does_not_affect_other_finds_on_old_version() {
    let mut ctx = VerificationContext::new();
    // v0: deep chain 3 → 2 → 1 → 0
    assume_parent_version(&mut ctx, "v0", &[0, 0, 1, 2]);
    // v1: after full compression of find(3): all nodes point to 0
    assume_parent_version(&mut ctx, "v1", &[0, 0, 0, 0]);

    // Compression shortens find(2) only in the new version, but both versions still
    // reach the same root.
    ctx.push_assert(
        "find2_old_and_new_versions_share_root",
        "v0.index(v0.index(v0.index(2))) == v1.index(v1.index(2))",
    );
    ctx.push_assert(
        "compression_shortens_element2_path",
        "v0.index(2) != v1.index(2)",
    );
    ctx.push_assert(
        "compressed_find2_root_is_stable",
        "v1.index(v1.index(2)) == v1.index(2)",
    );
    ctx.push_assert("element1_frame_is_preserved", "v1.index(1) == v0.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 48d: compression does not affect finds on old version, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Rollback / branching history
// ========================================================================

/// Tier 48e: branching from v0 — two independent unions from the same base.
///
/// v0 = [0, 1, 2, 3]
/// v1 = union(v0, 0, 1) = [1, 1, 2, 3]
/// v2 = union(v0, 2, 3) = [0, 1, 3, 3]
/// v1 and v2 are independent branches; v0 is shared root.
#[test]
fn test_vt_tier48e_branching_independent_unions_from_same_base() {
    let mut ctx = VerificationContext::new();
    assume_parent_version(&mut ctx, "v0", &[0, 1, 2, 3]);
    assume_parent_version(&mut ctx, "v1", &[1, 1, 2, 3]);
    assume_parent_version(&mut ctx, "v2", &[0, 1, 3, 3]);

    // Each branch merges a different pair while preserving the untouched branch.
    ctx.push_assert("v1_merges_0_into_1", "v1.index(v0.index(0)) == v0.index(1)");
    ctx.push_assert(
        "v1_preserves_other_branch",
        "v1.index(2) == v0.index(2) && v1.index(3) == v0.index(3)",
    );
    ctx.push_assert("v2_merges_2_into_3", "v2.index(v0.index(2)) == v0.index(3)");
    ctx.push_assert(
        "v2_preserves_other_branch",
        "v2.index(0) == v0.index(0) && v2.index(1) == v0.index(1)",
    );
    ctx.push_assert(
        "branches_choose_different_component_roots",
        "v1.index(v1.index(0)) != v2.index(v2.index(0))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 48e: branching independent unions should verify, got: {:?}",
        result,
    );
}

/// Tier 48f: rollback — operate on v0 after v1 and v2 exist.
///
/// v0 = [0, 1, 2, 3]
/// v1 = union(v0, 0, 1) = [1, 1, 2, 3]
/// v2 = union(v1, 2, 3) = [1, 1, 3, 3]
/// v3 = union(v0, 0, 2) = [2, 1, 2, 3] — rolled back to v0!
#[test]
fn test_vt_tier48f_rollback_to_earlier_version() {
    let mut ctx = VerificationContext::new();
    assume_parent_version(&mut ctx, "v0", &[0, 1, 2, 3]);
    assume_parent_version(&mut ctx, "v1", &[1, 1, 2, 3]);
    assume_parent_version(&mut ctx, "v2", &[1, 1, 3, 3]);
    // v3 branches from v0 (rollback), not v2
    assume_parent_version(&mut ctx, "v3", &[2, 1, 2, 3]);

    // v3 uses v0 as its base, so it merges 0 into 2 while keeping 1 and 3 at v0.
    ctx.push_assert("v3_uses_v0_as_base", "v3.index(v0.index(0)) == v0.index(2)");
    ctx.push_assert("v3_preserves_v0_elem1", "v3.index(1) == v0.index(1)");
    ctx.push_assert("v3_preserves_v0_elem3", "v3.index(3) == v0.index(3)");
    ctx.push_assert(
        "rollback_branch_differs_from_v1_history",
        "v3.index(v3.index(0)) != v1.index(v1.index(0))",
    );
    ctx.push_assert(
        "v2_history_is_unaffected_by_rollback_branch",
        "v2.index(v2.index(0)) == v1.index(v1.index(0))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 48f: rollback to earlier version should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Multi-step persistent traces
// ========================================================================

/// Tier 48g: sequential persistent unions — build v0 → v1 → v2,
/// then verify all three versions have the expected component structure.
///
/// v0 = [0, 1, 2, 3] (4 singletons)
/// v1 = union(v0, 0, 1) = [1, 1, 2, 3] ({0,1} merged)
/// v2 = union(v1, 2, 0) = [1, 1, 1, 3] ({0,1,2} merged)
#[test]
fn test_vt_tier48g_sequential_persistent_unions() {
    let mut ctx = VerificationContext::new();
    assume_parent_version(&mut ctx, "v0", &[0, 1, 2, 3]);
    assume_parent_version(&mut ctx, "v1", &[1, 1, 2, 3]);
    // union(v1, 2, 0): find(2,v1)=2, find(0,v1)=1 => v2[2]=1
    assume_parent_version(&mut ctx, "v2", &[1, 1, 1, 3]);

    // The first union merges {0,1}; the second extends that component to include 2
    // while leaving 3 untouched.
    ctx.push_assert(
        "v0_starts_as_singletons",
        "v0.index(v0.index(0)) == v0.index(0) && v0.index(v0.index(3)) == v0.index(3)",
    );
    ctx.push_assert(
        "v1_merges_first_pair",
        "v1.index(v1.index(0)) == v1.index(1)",
    );
    ctx.push_assert(
        "v2_extends_component_to_2",
        "v2.index(v2.index(2)) == v2.index(v2.index(0))",
    );
    ctx.push_assert(
        "second_union_changes_element2",
        "v2.index(2) != v1.index(2)",
    );
    ctx.push_assert(
        "second_union_preserves_unrelated_3",
        "v2.index(3) == v1.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 48g: sequential persistent unions should verify, got: {:?}",
        result,
    );
}

/// Tier 48h: persistent union + find with frame condition —
/// symbolic version transition with quantified frame.
///
/// Given v0 with n elements, union(v0, x, y) -> v1 where:
///   v1[find(x)] = find(y)
///   forall k != find(x): v1[k] == v0[k]
#[test]
fn test_vt_tier48h_symbolic_persistent_union_frame() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("v0", "Seq<u64>");
    ctx.declare_var_parsed("v1", "Seq<u64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("rx", "u64");
    ctx.declare_var_parsed("ry", "u64");
    ctx.declare_var_parsed("e", "u64");

    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("v0_len", "v0.len() == n");
    ctx.push_assume("v1_len", "v1.len() == n");
    ctx.push_assume("rx_bounds", "rx < n");
    ctx.push_assume("ry_bounds", "ry < n");
    ctx.push_assume("e_bounds", "e < n");
    ctx.push_assume("rx_is_root", "v0.index(rx) == rx");
    ctx.push_assume("ry_is_root", "v0.index(ry) == ry");
    ctx.push_assume("rx_neq_ry", "rx != ry");

    // Persistent union: v1[rx] = ry, frame for all other positions
    ctx.push_assume("union_link", "v1.index(rx) == ry");
    ctx.push_assume(
        "union_frame",
        "forall(|k: u64| !(k < n && k != rx) || v1.index(k) == v0.index(k))",
    );

    // Witness e != rx should have same parent in both versions
    ctx.push_assume("e_not_rx", "e != rx");
    ctx.push_assert("frame_holds_for_e", "v1.index(e) == v0.index(e)");

    // Because ry is preserved by the frame when rx != ry, the new link reaches a
    // stable root in one extra step rather than just echoing the link assumption.
    ctx.push_assert(
        "union_link_reaches_preserved_root",
        "v1.index(v1.index(rx)) == ry",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 48h: symbolic persistent union frame should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Soundness negatives
// ========================================================================

/// Tier 48i: version confusion — claiming v0 reflects the union is wrong.
///
/// v0 = [0, 1, 2, 3], v1 = union(v0, 0, 1) = [1, 1, 2, 3]
/// WRONG: v0[0] == 1 (that's v1, not v0)
#[test]
fn test_vt_tier48i_version_confusion_rejected() {
    let mut ctx = VerificationContext::new();
    assume_parent_version(&mut ctx, "v0", &[0, 1, 2, 3]);
    assume_parent_version(&mut ctx, "v1", &[1, 1, 2, 3]);

    // WRONG: claiming v0 was mutated by the persistent union
    ctx.push_assert("wrong_v0_mutation", "v0.index(0) == 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 48i SOUNDNESS: version confusion should be rejected, got: {:?}",
        result,
    );
}

/// Tier 48j: missing frame — after union, non-linked positions should be
/// preserved but without frame conditions this is unconstrained.
#[test]
fn test_vt_tier48j_missing_frame_allows_corruption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("v0", "Seq<u64>");
    ctx.declare_var_parsed("v1", "Seq<u64>");

    ctx.push_assume("v0_len", "v0.len() == 4");
    ctx.push_assume("v1_len", "v1.len() == 4");
    ctx.push_assume("v0_0", "v0.index(0) == 0");
    ctx.push_assume("v0_1", "v0.index(1) == 1");
    ctx.push_assume("v0_2", "v0.index(2) == 2");
    ctx.push_assume("v0_3", "v0.index(3) == 3");

    // Union link only — NO frame conditions
    ctx.push_assume("union_link", "v1.index(0) == 1");

    // WRONG: claim frame holds without assuming it
    ctx.push_assert("wrong_frame", "v1.index(2) == 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 48j SOUNDNESS: missing frame should be rejected, got: {:?}",
        result,
    );
}

/// Tier 48k: wrong rollback — using v2's state when claiming to roll back to v0.
///
/// v0 = [0,1,2,3], v1 = [1,1,2,3], v2 = [1,1,3,3]
/// WRONG: claiming v3 "rolled back to v0" but v3[0]==1 (which is from v1, not v0)
#[test]
fn test_vt_tier48k_wrong_rollback_rejected() {
    let mut ctx = VerificationContext::new();
    assume_parent_version(&mut ctx, "v0", &[0, 1, 2, 3]);
    assume_parent_version(&mut ctx, "v1", &[1, 1, 2, 3]);
    assume_parent_version(&mut ctx, "v2", &[1, 1, 3, 3]);
    // v3 claims to be union(v0, 2, 3) but uses v1's data for elem 0
    assume_parent_version(&mut ctx, "v3", &[1, 1, 3, 3]);

    // WRONG: claiming v3 was derived from v0 (rollback) but v3[0]==1 != v0[0]==0
    // If truly from v0, then for indices not involved in union(2,3), v3[i]==v0[i]
    ctx.push_assert("wrong_rollback_frame", "v3.index(0) == v0.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 48k SOUNDNESS: wrong rollback should be rejected, got: {:?}",
        result,
    );
}

/// Tier 48l: compression must not merge components — compressing find(3)
/// should not change the root of element 3's component.
#[test]
fn test_vt_tier48l_compression_must_not_merge_components() {
    let mut ctx = VerificationContext::new();
    // v0: {0,2,3} component (root 0), {1} singleton
    assume_parent_version(&mut ctx, "v0", &[0, 1, 0, 2]);
    // v1: after compressing find(3): 3 → 0 directly, 2 → 0 (unchanged)
    assume_parent_version(&mut ctx, "v1", &[0, 1, 0, 0]);

    // WRONG: claiming compression merged {1} into {0,2,3}
    ctx.push_assert("wrong_merge_claim", "v1.index(1) == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 48l SOUNDNESS: compression must not merge components, got: {:?}",
        result,
    );
}
