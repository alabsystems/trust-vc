//! Collection axiom encoding tests (#1800).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests for the collection axiom background assertions added in
//! `collection_axioms.rs` and wired into collection operations.
//! Covers Slice 1 (extensional equality) and Slice 2 (length axioms)
//! from `designs/2026-03-19-1800-collection-axiom-encoding.md`.

use super::*;

// ========================================================================
// Slice 1: Extensional equality encoder tests
// ========================================================================

/// CORRECTNESS: ext_eq! on two Seq variables with same length and same
/// elements at all indices should verify.
///
/// This tests the full pipeline: ext_eq! macro → IR lowering → TrustVcExpr
/// (forall + CollectionOp::Len + CollectionOp::Get) → ay encoding.
/// Requires bounded length to prevent push overflow guard from firing
/// (max u64 length + 1 wraps).
#[test]
fn test_seq_ext_eq_same_push_sequence_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("bounded_len", "s.len() < 100"));
    // Two sequences built identically: both push 42 onto s.
    ctx.push_obligation(ProofObligation::assert(
        "ext_eq_same",
        "ext_eq!(s.push(42), s.push(42))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ext_eq!(s.push(42), s.push(42)) should verify — same construction (#1800)",
    );
}

/// DISCRIMINATING: ext_eq! on two Seq variables with different lengths
/// must NOT verify. Proves ext_eq is not vacuously true.
#[test]
fn test_seq_ext_eq_different_length_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len1", "s1.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("len2", "s2.len() == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "ext_eq_wrong_len",
        "ext_eq!(s1, s2)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "ext_eq! on sequences with different lengths should NOT verify (#1800)",
    );
}

/// CORRECTNESS: ext_eq! on two Set variables where membership is
/// identical should verify. Uses insert to construct matching sets.
#[test]
fn test_set_ext_eq_same_membership_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    // Both sides insert the same element — identical set.
    ctx.push_obligation(ProofObligation::assert(
        "set_ext_eq_same",
        "ext_eq!(s.insert(5), s.insert(5))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ext_eq!(s.insert(5), s.insert(5)) should verify — same construction (#1800)",
    );
}

/// DISCRIMINATING: ext_eq! on two Set variables with different insertions
/// must NOT verify (one has element 5, other has element 10 — different
/// membership for base set elements not controlled).
#[test]
fn test_set_ext_eq_different_inserts_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    // s.insert(5) and s.insert(10) differ at element 5 and 10
    // (unless s already contains both, which is unknown).
    ctx.push_obligation(ProofObligation::assume("not_in_s_5", "!s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "set_ext_eq_wrong",
        "ext_eq!(s.insert(5), s.insert(10))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "ext_eq! on sets with different insertions (and 5 not in s) should NOT verify (#1800)",
    );
}

// ========================================================================
// Slice 2: Explicit length axiom tests
// ========================================================================

/// CORRECTNESS: push length axiom is explicitly asserted, not just
/// implicitly constructed. Verifies that the length relationship
/// `push(s, v).len() == s.len() + 1` is available to the solver.
#[test]
fn test_push_length_axiom_explicit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("known_len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert("push_len", "s.push(99).len() == 6"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "push length axiom: s.push(99).len() == s.len() + 1 (#1800)",
    );
}

/// DISCRIMINATING: wrong push length must NOT verify.
#[test]
fn test_push_length_axiom_wrong_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("known_len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "push_wrong",
        "s.push(99).len() == 5",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "push(s, v).len() == s.len() (not s.len()+1) should NOT verify (#1800)",
    );
}

/// CORRECTNESS: update preserves length — `s.update(i, v).len() == s.len()`.
#[test]
fn test_update_preserves_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "update_len",
        "s.update(1, 42).len() == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "update preserves length (#1800)");
}

/// CORRECTNESS: concat length axiom — `s1.concat(s2).len() == s1.len() + s2.len()`.
#[test]
fn test_concat_length_axiom_explicit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len1", "s1.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("len2", "s2.len() == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "concat_len",
        "s1.concat(s2).len() == 7",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "concat length axiom: 3 + 4 == 7 (#1800)");
}

/// DISCRIMINATING: concat wrong length must NOT verify.
#[test]
fn test_concat_length_axiom_wrong_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len1", "s1.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("len2", "s2.len() == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "concat_wrong",
        "s1.concat(s2).len() == 6",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "concat length 3 + 4 != 6 should NOT verify (#1800)",
    );
}

/// CORRECTNESS: chained push length — verifies length axiom works
/// across multiple operations.
#[test]
fn test_chained_push_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("empty", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "double_push",
        "s.push(1).push(2).len() == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chained push: len 0 + 2 pushes == 2 (#1800)");
}

/// DISCRIMINATING: chained push with wrong expected length.
#[test]
fn test_chained_push_wrong_length_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("empty", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "double_push_wrong",
        "s.push(1).push(2).len() == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "chained push len 0 + 2 != 3 should NOT verify (#1800)",
    );
}

// ========================================================================
// #2531: Safe quantifier regression tests for Set<u32> operations
// ========================================================================

/// CORRECTNESS: Set<u32>::union uses safe quantifier pattern (#2531).
/// If s1 contains element 1u32, union(s1, s2) must also contain 1u32.
/// Exercises BV-sorted quantifier instantiation for unsigned element types.
#[test]
fn test_set_u32_union_safe_quantifier_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<u32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<u32>"));
    ctx.push_obligation(ProofObligation::assume("s1_has_1", "s1.contains(1)"));
    ctx.push_obligation(ProofObligation::assert(
        "union_has_1",
        "s1.union(s2).contains(1)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Set<u32>::union should preserve membership with safe quantifier (#2531)",
    );
}

/// DISCRIMINATING: Set<u32>::union must reject false membership (#2531).
#[test]
fn test_set_u32_union_rejects_absent_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<u32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<u32>"));
    ctx.push_obligation(ProofObligation::assume("s1_not_99", "!s1.contains(99)"));
    ctx.push_obligation(ProofObligation::assume("s2_not_99", "!s2.contains(99)"));
    ctx.push_obligation(ProofObligation::assert(
        "union_has_99",
        "s1.union(s2).contains(99)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Set<u32>::union must not contain absent element with safe quantifier (#2531)",
    );
}

/// CORRECTNESS: Set<u32>::intersect uses safe quantifier pattern (#2531).
#[test]
fn test_set_u32_intersect_safe_quantifier_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<u32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<u32>"));
    ctx.push_obligation(ProofObligation::assume("s1_has_42", "s1.contains(42)"));
    ctx.push_obligation(ProofObligation::assume("s2_has_42", "s2.contains(42)"));
    ctx.push_obligation(ProofObligation::assert(
        "intersect_has_42",
        "s1.intersect(s2).contains(42)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Set<u32>::intersect should contain common element with safe quantifier (#2531)",
    );
}

/// DISCRIMINATING: Set<u32>::intersect must reject non-common element (#2531).
#[test]
fn test_set_u32_intersect_rejects_non_common() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<u32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<u32>"));
    ctx.push_obligation(ProofObligation::assume("s1_has_5", "s1.contains(5)"));
    ctx.push_obligation(ProofObligation::assume("s2_not_5", "!s2.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "intersect_has_5",
        "s1.intersect(s2).contains(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Set<u32>::intersect must not contain non-common element (#2531)",
    );
}
