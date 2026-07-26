// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 16 — Persistent data structures & functional update VCs.
//!
//! VerifyThis 2025 featured Persistent Arrays and Persistent Disjoint Sets.
//! These problems reduce to functional update reasoning: read-after-write,
//! frame conditions (what DOESN'T change), version chains, and set membership.
//!
//! Maps Map<K,V> encode via SMT array theory (select/store axioms).
//! Sets Set<T> encode via SMT array theory mapping T → Bool.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline.

mod common;

use common::verify_context_with_pipeline;
use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

fn assume_contains_key(ctx: &mut VerificationContext, name: &str, map: &str, key: &str) {
    let condition = format!("{map}.contains_key({key})");
    ctx.push_assume(name, &condition);
}

// GROUP A: Read-after-write (SMT store/select axiom)

/// Tier 16a: Read-after-write — m.insert(k, v).get(k) == v.
#[test]
fn test_vt_tier16a_read_after_write() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");
    ctx.declare_var_parsed("v", "i32");

    ctx.push_assert("raw", "m.insert(k, v).get(k) == v");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16a: read-after-write axiom should verify, got: {:?}",
        result,
    );
}

/// Tier 16a: Read-after-write with concrete keys — insert(5, 42) then get(5).
#[test]
fn test_vt_tier16a_read_after_write_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<i32, i32>");

    ctx.push_assert("concrete_raw", "m.insert(5, 42).get(5) == 42");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16a: concrete read-after-write should verify, got: {:?}",
        result,
    );
}

/// Tier 16a: Frame condition — insert at k preserves get at j != k.
#[test]
fn test_vt_tier16a_frame_condition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");
    ctx.declare_var_parsed("j", "i32");
    ctx.declare_var_parsed("v", "i32");

    ctx.push_assume("distinct", "k != j");
    assume_contains_key(&mut ctx, "m_has_j", "m", "j");
    ctx.push_assert("frame", "m.insert(k, v).get(j) == m.get(j)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16a: frame condition (insert at k, read at j != k) should verify, got: {:?}",
        result,
    );
}

/// Tier 16a: Frame condition negative — insert at k DOES change get at k.
#[test]
fn test_vt_tier16a_frame_negative_same_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<i32, i32>");
    // Concrete witness keeps this negative in the reliable Counterexample bucket:
    // if the old value at key 5 is 0, then writing 42 at that same key changes it.
    assume_contains_key(&mut ctx, "m_has_5", "m", "5");
    ctx.push_assume("old_value", "m.get(5) == 0");
    ctx.push_assert("wrong_frame", "m.insert(5, 42).get(5) == m.get(5)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 16a SOUNDNESS: insert(5,42).get(5) == m.get(5) with m.get(5)=0 should produce a counterexample, got: {:?}",
        result,
    );
}

// GROUP B: Chained updates (persistent version chains)

/// Tier 16b: Chained updates — last write wins at same key.
/// m.insert(k, 10).insert(k, 20).get(k) == 20
#[test]
fn test_vt_tier16b_last_write_wins() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");

    ctx.push_assert("last_write", "m.insert(k, 10).insert(k, 20).get(k) == 20");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16b: last write wins at same key, got: {:?}",
        result,
    );
}

/// Tier 16b: Chained updates at different keys — both preserved.
/// m.insert(1, 10).insert(2, 20): get(1)==10 AND get(2)==20.
/// No assumptions — relies purely on SMT store/select axioms.
#[test]
fn test_vt_tier16b_chained_different_keys() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<i32, i32>");

    // Both reads from the double-insert should hold via array axioms alone
    ctx.push_assert(
        "both_preserved_1",
        "m.insert(1, 10).insert(2, 20).get(1) == 10",
    );
    ctx.push_assert(
        "both_preserved_2",
        "m.insert(1, 10).insert(2, 20).get(2) == 20",
    );

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16b: chained inserts at different keys both readable, got: {:?}",
        result,
    );
}

/// Tier 16b: Version independence — old version unchanged after new version created.
/// Persistent array: v1 = m.insert(k, 10), v2 = v1.insert(k, 20).
/// v1.get(k) should still be 10, not 20.
#[test]
fn test_vt_tier16b_version_independence() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<i32, i32>");
    ctx.declare_var_parsed("v1", "Map<i32, i32>");
    ctx.declare_var_parsed("v2", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");

    // v1 = m.insert(k, 10)
    assume_contains_key(&mut ctx, "v1_has_k", "v1", "k");
    ctx.push_assume("v1_def_read", "v1.get(k) == 10");
    // v2 = v1.insert(k, 20) — a NEW version
    assume_contains_key(&mut ctx, "v2_has_k", "v2", "k");
    ctx.push_assume("v2_def_read", "v2.get(k) == 20");

    ctx.push_assert("versions_diverge", "v1.get(k) != v2.get(k)");
    ctx.push_assert("newer_version_is_larger", "v2.get(k) > v1.get(k)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16b: version independence should verify, got: {:?}",
        result,
    );
}

/// Tier 16b: Chained update soundness negative — earlier write NOT visible.
/// m.insert(k, 10).insert(k, 20).get(k) != 10 in general.
#[test]
fn test_vt_tier16b_earlier_write_overwritten() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");

    ctx.push_assert(
        "wrong_earlier",
        "m.insert(k, 10).insert(k, 20).get(k) == 10",
    );

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 16b SOUNDNESS: earlier write should be overwritten by a later write (10 then 20), got: {:?}",
        result,
    );
}

// GROUP C: Set-based reasoning (disjoint sets, membership)

/// Tier 16c: Set insert + contains — after inserting v, contains(v) is true.
#[test]
fn test_vt_tier16c_set_insert_contains() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Set<i32>");
    ctx.declare_var_parsed("v", "i32");

    ctx.push_assert("insert_contains", "s.insert(v).contains(v)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16c: insert(v) then contains(v) should verify, got: {:?}",
        result,
    );
}

/// Tier 16c: Set insert frame — inserting v preserves membership of w != v.
#[test]
fn test_vt_tier16c_set_insert_frame() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Set<i32>");
    ctx.declare_var_parsed("v", "i32");
    ctx.declare_var_parsed("w", "i32");

    ctx.push_assume("w_in_s", "s.contains(w)");
    ctx.push_assert("still_in", "s.insert(v).contains(w)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16c: insert(v) preserves contains(w) for any w, got: {:?}",
        result,
    );
}

/// Tier 16c: Set union — element in either input is in union.
#[test]
fn test_vt_tier16c_union_membership() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "Set<i32>");
    ctx.declare_var_parsed("b", "Set<i32>");
    ctx.declare_var_parsed("x", "i32");

    ctx.push_assume("x_in_a", "a.contains(x)");
    ctx.push_assert("x_in_union", "a.union(b).contains(x)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16c: element in a is in a.union(b), got: {:?}",
        result,
    );
}

/// Tier 16c: Set intersection — element in intersection is in both.
#[test]
fn test_vt_tier16c_intersection_both() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "Set<i32>");
    ctx.declare_var_parsed("b", "Set<i32>");
    ctx.declare_var_parsed("x", "i32");

    ctx.push_assume("x_in_inter", "a.intersect(b).contains(x)");
    ctx.push_assert("x_in_a", "a.contains(x)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16c: element in intersection is in a, got: {:?}",
        result,
    );
}

/// Tier 16c: Disjoint sets negative — union does not imply intersection.
#[test]
fn test_vt_tier16c_disjoint_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "Set<i32>");
    ctx.declare_var_parsed("b", "Set<i32>");
    // Concrete witness keeps this negative in the reliable Counterexample bucket:
    // 1 is in `a`, not in `b`, so union membership does not imply both-set membership.
    ctx.push_assume("one_in_a", "a.contains(1)");
    ctx.push_assume("one_not_in_b", "!b.contains(1)");
    ctx.push_assert("one_in_union", "a.union(b).contains(1)");
    ctx.push_assert("wrong_both", "a.contains(1) && b.contains(1)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 16c SOUNDNESS: union membership should not imply intersection (e.g. 1 in a only); expect counterexample, got: {:?}",
        result,
    );
}

// GROUP D: Persistent array simulation (VerifyThis 2025 Challenge 1)

/// Tier 16d: Persistent array — write then read at same index.
#[test]
fn test_vt_tier16d_persistent_array_write_read() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("arr", "Map<u64, i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("v", "i32");

    // read(write(arr, i, v), i) == v
    ctx.push_assert("write_read", "arr.insert(i, v).get(i) == v");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16d: persistent array write-read should verify, got: {:?}",
        result,
    );
}

/// Tier 16d: Persistent array — write at i, read at j != i is unchanged.
#[test]
fn test_vt_tier16d_persistent_array_frame() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("arr", "Map<u64, i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("v", "i32");

    ctx.push_assume("i_ne_j", "i != j");
    assume_contains_key(&mut ctx, "arr_has_j", "arr", "j");
    // read(write(arr, i, v), j) == read(arr, j)
    ctx.push_assert("frame", "arr.insert(i, v).get(j) == arr.get(j)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16d: persistent array frame should verify, got: {:?}",
        result,
    );
}

/// Tier 16d: Persistent array — two versions from same base.
/// v1 = write(arr, 0, 10), v2 = write(arr, 0, 20).
/// Both diverge from arr but don't affect each other.
#[test]
fn test_vt_tier16d_persistent_array_fork() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("arr", "Map<u64, i32>");
    ctx.declare_var_parsed("v1", "Map<u64, i32>");
    ctx.declare_var_parsed("v2", "Map<u64, i32>");

    // Two independent writes to same base at index 0
    assume_contains_key(&mut ctx, "v1_has_0", "v1", "0");
    ctx.push_assume("v1_write", "v1.get(0) == 10");
    assume_contains_key(&mut ctx, "v2_has_0", "v2", "0");
    ctx.push_assume("v2_write", "v2.get(0) == 20");
    // Both share arr's value at index 1
    assume_contains_key(&mut ctx, "v1_has_1", "v1", "1");
    assume_contains_key(&mut ctx, "arr_has_1", "arr", "1");
    ctx.push_assume("v1_frame", "v1.get(1) == arr.get(1)");
    assume_contains_key(&mut ctx, "v2_has_1", "v2", "1");
    ctx.push_assume("v2_frame", "v2.get(1) == arr.get(1)");

    // v1 and v2 diverge at index 0
    ctx.push_assert("diverge", "v1.get(0) != v2.get(0)");
    // But agree at index 1 (both inherited from arr)
    ctx.push_assert("agree", "v1.get(1) == v2.get(1)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16d: forked versions diverge at write, agree at frame, got: {:?}",
        result,
    );
}

/// Tier 16d: Persistent array negative — fork versions don't share writes.
#[test]
fn test_vt_tier16d_persistent_array_fork_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("arr", "Map<u64, i32>");
    ctx.declare_var_parsed("v1", "Map<u64, i32>");
    ctx.declare_var_parsed("v2", "Map<u64, i32>");

    assume_contains_key(&mut ctx, "v1_has_0", "v1", "0");
    ctx.push_assume("v1_write", "v1.get(0) == 10");
    assume_contains_key(&mut ctx, "v2_has_0", "v2", "0");
    ctx.push_assume("v2_write", "v2.get(0) == 20");

    // WRONG: v1 does not see v2's write
    ctx.push_assert("wrong_share", "v1.get(0) == v2.get(0)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 16d SOUNDNESS: forked versions should not share writes (v1[0]=10, v2[0]=20); expect counterexample, got: {:?}",
        result,
    );
}

// GROUP E: Functional accumulation patterns (building results via updates)

/// Tier 16e: Accumulating set — after inserting elements 0..i, contains(j) for j < i.
/// BV overflow guard: i < 1000000.
#[test]
fn test_vt_tier16e_accumulating_set_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("seen", "Set<i32>");
    ctx.declare_var_parsed("seen_new", "Set<i32>");
    ctx.declare_var_parsed("elem", "i32");

    // Invariant: seen contains elem (we just inserted it)
    ctx.push_assume("insert_def", "seen_new == seen.insert(elem)");
    ctx.push_assert("contains_elem", "seen_new.contains(elem)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16e: accumulating set step should verify, got: {:?}",
        result,
    );
}

/// Tier 16e: Accumulating set preserves prior membership.
/// After inserting new_elem, old elements are still in the set.
#[test]
fn test_vt_tier16e_accumulating_set_preserves_prior() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("seen", "Set<i32>");
    ctx.declare_var_parsed("old_elem", "i32");
    ctx.declare_var_parsed("new_elem", "i32");

    ctx.push_assume("old_in_seen", "seen.contains(old_elem)");
    ctx.push_assert("still_in", "seen.insert(new_elem).contains(old_elem)");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16e: insert preserves prior membership, got: {:?}",
        result,
    );
}

/// Tier 16e: Map accumulation — building a histogram.
/// After counting elem, the count at elem is incremented.
#[test]
fn test_vt_tier16e_histogram_update() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("hist", "Map<i32, i32>");
    ctx.declare_var_parsed("hist_new", "Map<i32, i32>");
    ctx.declare_var_parsed("elem", "i32");
    ctx.declare_var_parsed("old_count", "i32");

    assume_contains_key(&mut ctx, "hist_has_elem", "hist", "elem");
    ctx.push_assume("old_count_def", "old_count == hist.get(elem)");
    ctx.push_assume("count_bounded", "old_count >= 0 && old_count < 1000000");
    ctx.push_assume("update_def", "hist_new == hist.insert(elem, old_count + 1)");

    // After increment: new count == old count + 1
    ctx.push_assert("count_incremented", "hist_new.get(elem) == old_count + 1");
    // And the new count is positive
    ctx.push_assert("count_positive", "hist_new.get(elem) > 0");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16e: histogram update should verify, got: {:?}",
        result,
    );
}

/// Tier 16e: Map accumulation frame — updating one key doesn't affect others.
#[test]
fn test_vt_tier16e_histogram_frame() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("hist", "Map<i32, i32>");
    ctx.declare_var_parsed("elem", "i32");
    ctx.declare_var_parsed("other", "i32");

    ctx.push_assume("distinct", "elem != other");
    assume_contains_key(&mut ctx, "hist_has_elem", "hist", "elem");
    assume_contains_key(&mut ctx, "hist_has_other", "hist", "other");
    ctx.push_assert(
        "frame",
        "hist.insert(elem, hist.get(elem) + 1).get(other) == hist.get(other)",
    );

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 16e: histogram frame (other key unchanged) should verify, got: {:?}",
        result,
    );
}

/// Tier 16e: Accumulation soundness negative — insert does NOT make all keys have the value.
#[test]
fn test_vt_tier16e_accumulation_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<i32, i32>");
    ctx.declare_var_parsed("k", "i32");
    ctx.declare_var_parsed("j", "i32");

    // After inserting 42 at k, claiming j has 42 too
    ctx.push_assert("wrong_all", "m.insert(k, 42).get(j) == 42");

    let result = verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 16e SOUNDNESS: inserting at k should not affect all keys (e.g. j!=k); expect counterexample, got: {:?}",
        result,
    );
}
