//! Cross-width coercion and sort mismatch tests for collection operations.
//! Covers #1752 (index/get term_widths), #1888 (Int vs BitVec(64) index
//! sort mismatch), #1932 (BV32 vs Int element sort mismatch),
//! #1744 (Seq::contains cross-width BV coercion).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from collections/mod.rs (#2145).

use super::*;

// ========================================================================
// Seq index/get term_widths registration (#1752)
// ========================================================================

/// REGRESSION: Seq::index() result must be registered in term_widths for
/// cross-width coercion. Without registration, comparing a Seq<i64> element
/// with a u32 variable would fail to coerce widths, producing ay sort
/// mismatch panics or incorrect verification results.
/// Fixes #1752.
#[test]
fn test_seq_index_cross_width_comparison() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i64>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 1"));
    ctx.push_obligation(ProofObligation::assume("elem", "s.index(0) == 100"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    // This comparison requires width coercion: s.index(0) is i64, x is u32.
    // Without term_widths registration on index result, coercion fails.
    ctx.push_obligation(ProofObligation::assert("cross_width_eq", "s.index(0) == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq<i64>::index(0) == u32 should verify when both equal 100 (#1752)",
    );
}

/// REGRESSION: Seq::first() result must be registered in term_widths.
/// Same issue as index() — first() calls try_select without width registration.
/// Fixes #1752.
#[test]
fn test_seq_first_cross_width_comparison() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i64>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 1"));
    ctx.push_obligation(ProofObligation::assume("elem", "s.index(0) == 42"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "first_cross_width",
        "s.first() == x",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq<i64>::first() == u32 should verify when both equal 42 (#1752)",
    );
}

/// REGRESSION: Seq::last() result must be registered in term_widths.
/// Fixes #1752.
#[test]
fn test_seq_last_cross_width_comparison() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i64>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 1"));
    ctx.push_obligation(ProofObligation::assume("elem", "s.index(0) == 77"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 77"));
    ctx.push_obligation(ProofObligation::assert("last_cross_width", "s.last() == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq<i64>::last() == u32 should verify when both equal 77 (#1752)",
    );
}

/// REGRESSION: Map::get() result must be registered in term_widths.
/// Map<i32, i64>::get(k) returns i64 — must be tracked for cross-width ops.
/// Fixes #1752.
#[test]
fn test_map_get_cross_width_comparison() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i64>"),
    );
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("key_present", "m.contains_key(5)"));
    ctx.push_obligation(ProofObligation::assume("key_val", "m.get(5) == 99"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 99"));
    ctx.push_obligation(ProofObligation::assert(
        "map_get_cross_width",
        "m.get(5) == x",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Map<i32, i64>::get(5) == u32 should verify when both equal 99 (#1752)",
    );
}

// ========================================================================
// Seq index inside quantifier body — Int vs BitVec(64) sort mismatch (#1888)
// ========================================================================

/// REGRESSION: Seq::index() with a quantifier-bound variable must convert
/// the Sort::Int index to BitVec(64) via int2bv. Without the fix, the
/// Int-typed quantifier variable passes through coerce_seq_index unchanged,
/// causing a sort mismatch at try_select.
/// Fixes #1888.
#[test]
fn test_seq_index_in_quantifier_body() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 20"));
    ctx.push_obligation(ProofObligation::assume("elem2", "s.index(2) == 30"));
    // forall i: u64. !(i < 3) || s.index(i) >= 0
    // The quantifier-bound i has Sort::Int; s.index(i) needs int2bv(64) conversion.
    ctx.push_obligation(ProofObligation::assert(
        "all_nonneg",
        "forall(|i: u64| !(i < 3) || s.index(i) >= 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Seq index with quantifier-bound variable should verify after int2bv coercion.
    expect_verified(
        &result,
        "Seq index with quantifier-bound variable should encode without sort mismatch (#1888)",
    );
}

/// DISCRIMINATING: Seq::index() in quantifier with false property must NOT verify.
/// Ensures the int2bv conversion doesn't silently make everything true.
/// Fixes #1888.
#[test]
fn test_seq_index_in_quantifier_false_property_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == -5"));
    // forall i: u64. !(i < 2) || s.index(i) >= 0 — FALSE because s[1] == -5
    ctx.push_obligation(ProofObligation::assert(
        "all_nonneg_false",
        "forall(|i: u64| !(i < 2) || s.index(i) >= 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Seq index quantifier with negative element should NOT verify (#1888)",
    );
}

// ========================================================================
// Seq element sort in quantifier body — BV32 vs Int mismatch (#1932)
// ========================================================================

/// REGRESSION: Seq<i32> element compared to Int literal in quantifier body.
/// Without bv2int conversion, `s.index(0) >= 0` panics with:
///   sort mismatch in ge: got [BitVec(32), Int]
/// The fix converts BV32 elements to Sort::Int via bv2int_signed in int_mode.
/// Fixes #1932.
#[test]
fn test_seq_element_bv2int_in_quantifier_no_panic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 1"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 5"));
    // The quantifier body accesses s.index(i) and compares with Int literal 0.
    // Before #1932 fix, this panics during encoding with sort mismatch.
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "forall(|i: u64| !(i < 1) || s.index(i) >= 0)",
    ));
    let result = AYEncoder::verify(&ctx);
    // Seq element bv2int encoding verifies after #1932 sort mismatch fix.
    expect_verified(
        &result,
        "Seq element in quantifier body should encode without sort mismatch (#1932)",
    );
}

/// DISCRIMINATING: Seq<i32> with negative element in quantifier — must not verify.
/// Ensures bv2int_signed correctly represents -5 as a negative Int, so the
/// comparison `s.index(i) >= 0` correctly fails.
/// Fixes #1932.
#[test]
fn test_seq_element_bv2int_signed_preserves_negativity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 1"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == -5"));
    ctx.push_obligation(ProofObligation::assert(
        "all_nonneg_false",
        "forall(|i: u64| !(i < 1) || s.index(i) >= 0)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Seq element -5 compared >= 0 should NOT verify (#1932)",
    );
}

/// REGRESSION: Seq<u32> element in quantifier — unsigned bv2int.
/// u32 elements should use unsigned bv2int (not signed), so 0xFFFFFFFF
/// maps to 4294967295, not -1.
/// Fixes #1932.
#[test]
fn test_seq_element_bv2int_unsigned_in_quantifier() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<u32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 1"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "forall(|i: u64| !(i < 1) || s.index(i) >= 0)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq<u32> element in quantifier should encode without sort mismatch (#1932)",
    );
}

// ========================================================================
// Seq::contains cross-width BV coercion (#1744)
// ========================================================================

/// REGRESSION: Seq<i64>::contains(x) where x is i32 must coerce BV widths.
/// Without coerce_bv_widths, the existential body's equality compares
/// BV(64) (element) with BV(32) (value), causing a ay sort mismatch.
/// Fixes #1744.
#[test]
fn test_seq_contains_cross_width_encodes_without_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i64>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 1"));
    ctx.push_obligation(ProofObligation::assume("elem", "s.index(0) == 42"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    // contains(x) encodes exists i. select(s, i) == x.
    // select returns BV(64), x is BV(32) — requires coerce_bv_widths.
    ctx.push_obligation(ProofObligation::assert("check", "s.contains(x)"));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(&result, "Seq<i64>::contains(i32) cross-width (#1744)");
}

// ========================================================================
// Soundness: bounded forall over a constrained Seq — BOTH directions.
//
// A VALID universally-quantified element property over a Seq with known
// elements must VERIFY (never a false counterexample), and a GENUINELY-FALSE
// property must still be REFUTED. The former regressed when the symbolic
// quantifier witness `select(s, i)` decoupled from the ground element
// assumptions once the Route-A Int length atom poisoned the array+BV query;
// the fix ground-expands the concrete-bounded refutation so each read is at a
// literal index congruent to the assumptions.
// ========================================================================

/// SOUNDNESS (direction i): VALID `forall i<3. s[i] >= 0` over s=[10,20,30]
/// must Verify — no false counterexample. Mirrors the #1888 index-coercion
/// regression case.
#[test]
fn test_bounded_forall_valid_nonneg_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("e0", "s.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assume("e1", "s.index(1) == 20"));
    ctx.push_obligation(ProofObligation::assume("e2", "s.index(2) == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_nonneg",
        "forall(|i: u64| !(i < 3) || s.index(i) >= 0)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "valid bounded forall over constrained Seq must verify (no false cex)",
    );
}

/// SOUNDNESS (direction i): exact element-value property
/// `forall i<3. s[i] == 10*(i+1)` is too strong to phrase generically, so
/// assert a weaker exact bound that genuinely holds: every element is <= 30.
#[test]
fn test_bounded_forall_valid_upper_bound_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("e0", "s.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assume("e1", "s.index(1) == 20"));
    ctx.push_obligation(ProofObligation::assume("e2", "s.index(2) == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_upper",
        "forall(|i: u64| !(i < 3) || s.index(i) <= 30)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "valid bounded forall (<= 30) must verify");
}

/// SOUNDNESS (direction ii): GENUINELY-FALSE `forall i<3. s[i] >= 100` over
/// s=[10,20,30] must still REFUTE — the fix must not over-approximate true.
#[test]
fn test_bounded_forall_false_threshold_refutes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("e0", "s.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assume("e1", "s.index(1) == 20"));
    ctx.push_obligation(ProofObligation::assume("e2", "s.index(2) == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "false_threshold",
        "forall(|i: u64| !(i < 3) || s.index(i) >= 100)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "false bounded forall (>= 100) must NOT verify");
}

/// SOUNDNESS (direction ii): holds for SOME but not all indices —
/// `forall i<3. s[i] >= 20` is false at i=0 (s[0]==10). Must REFUTE.
#[test]
fn test_bounded_forall_partial_property_refutes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("e0", "s.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assume("e1", "s.index(1) == 20"));
    ctx.push_obligation(ProofObligation::assume("e2", "s.index(2) == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "partial",
        "forall(|i: u64| !(i < 3) || s.index(i) >= 20)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "bounded forall that fails at i=0 must NOT verify");
}

/// SOUNDNESS (direction iii): a symbolic Seq with a real counterexample — the
/// quantifier claims all elements positive but an element is pinned negative.
/// Must REFUTE.
#[test]
fn test_bounded_forall_symbolic_negative_element_refutes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 4"));
    ctx.push_obligation(ProofObligation::assume("e0", "s.index(0) == 1"));
    ctx.push_obligation(ProofObligation::assume("e1", "s.index(1) == 2"));
    ctx.push_obligation(ProofObligation::assume("e2", "s.index(2) == -7"));
    ctx.push_obligation(ProofObligation::assume("e3", "s.index(3) == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "all_positive",
        "forall(|i: u64| !(i < 4) || s.index(i) > 0)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "bounded forall with a pinned negative element must NOT verify",
    );
}
