//! Push/insert coercion (#1971), metadata overwrite regression (#2148),
//! push overflow guard (#2142), and concat negative test (#1804).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from collections/mod.rs (#2145).

use super::*;

// ========================================================================
// Seq concat negative test (#1804)
// ========================================================================

/// DISCRIMINATING: wrong concat length must NOT verify (#1804).
/// Asserts s1.concat(s2).len() == s1.len() (ignoring rhs), which should fail.
#[test]
fn test_seq_concat_wrong_length_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len1", "s1.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("len2", "s2.len() == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "wrong_len",
        "s1.concat(s2).len() == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "s1.concat(s2).len() == 2 should NOT verify (correct is 5)",
    );
}

/// CORRECTNESS: upstream seqs.rs test1-style subrange/add length composition.
///
/// Mirrors the finite part of `let s3 = s.subrange(1, 4); let s5 = s3.add(t);`
/// where both original sequences have length 5, so the result length is 3 + 5.
#[test]
fn test_seq_subrange_add_length_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("t", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("s_len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assume("t_len", "t.len() == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "subrange_add_len",
        "s.subrange(1, 4).add(t).len() == 8",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s.subrange(1, 4).add(t).len() should verify as 3 + 5",
    );
}

// ========================================================================
// Push/insert value coercion (#1971)
// ========================================================================

// Int-to-BV store coercion direct encoder tests (#1936, #1953) moved to
// collections_encoder_direct.rs for file size compliance (#1972).
// Bounds check targeting tests (#2231) also moved there.

/// CORRECTNESS (#1971): Seq::push coerces value correctly — verifiable ground case.
/// The push stores value 42 (BV32 via coercion) at index==len. If the
/// coercion produced the wrong BV width, ay would sort-mismatch at try_store
/// and return Unknown instead of Verified. This companion test covers the
/// push value coercion path that test_seq_push_in_quantifier_body_no_panic
/// cannot verify due to ay-dpll exists limitations.
#[test]
fn test_seq_push_value_coercion_correct() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    // Verify push produces correct length — proves the store operation
    // completed without sort mismatch from incorrect value coercion.
    ctx.push_obligation(ProofObligation::assert("push_len", "s.push(42).len() == 3"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::push(42) should produce len==3 — value coercion correctness (#1971)",
    );
}

/// DISCRIMINATING (#1971): Seq::push with wrong expected length must NOT verify.
/// Ensures the push correctness test is not vacuously true.
#[test]
fn test_seq_push_wrong_length_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "push_wrong_len",
        "s.push(42).len() == 4",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Seq::push(42) on len-2 should NOT produce len==4 (#1971)",
    );
}

/// CORRECTNESS (#1971): Set::insert coerces key correctly — verifiable ground case.
/// Set<i32> has BV32 key sort. The insert stores a coerced key. If the
/// coercion produced the wrong BV width, contains would fail to find it.
/// This companion test covers the set key coercion path that
/// test_set_contains_key_coerced_in_quantifier_body cannot verify due to
/// ay-dpll quantifier BV limitations.
#[test]
fn test_set_insert_key_coercion_correct() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    // Insert a value, then verify it's in the set.
    // Ground (non-quantifier) case that exercises the same store coercion.
    ctx.push_obligation(ProofObligation::assert(
        "insert_then_contains",
        "s.insert(10).contains(10)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Set::insert(10).contains(10) should verify — key coercion correctness (#1971)",
    );
}

/// DISCRIMINATING (#1971): Set::insert key, check for different key must NOT verify.
/// Ensures the set insert correctness test is not vacuously true.
#[test]
fn test_set_insert_key_wrong_lookup_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    // Insert 10, then check for 20 — should NOT verify (20 may not be in s).
    ctx.push_obligation(ProofObligation::assert(
        "insert_wrong_lookup",
        "s.insert(10).contains(20)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Set::insert(10).contains(20) should NOT verify (#1971)",
    );
}

// ========================================================================
// Seq metadata overwrite regression tests (#2148)
// ========================================================================

/// REGRESSION: drop_last() must not corrupt source sequence length.
///
/// Before #2148 fix, `s.drop_last()` overwrote `collection_lengths["s"]`
/// to `len-1`, so the RHS `s.len() - 1` became `(len-1) - 1 = len-2`,
/// causing the assertion to fail. The fix creates a fresh array term so
/// the source metadata is preserved.
#[test]
fn test_seq_drop_last_preserves_source_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("nonempty", "s.len() >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "drop_last_vs_source",
        "s.drop_last().len() == s.len() - 1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s.drop_last().len() == s.len() - 1 should verify (#2148)",
    );
}

/// REGRESSION: take() must not corrupt source sequence length.
///
/// Before #2148 fix, `s.take(n)` overwrote `collection_lengths["s"]`
/// to `n`, so subsequent references to `s.len()` read `n` instead
/// of the original length.
#[test]
fn test_seq_take_preserves_source_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "take_vs_source",
        "s.take(3).len() + s.len() == 8",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s.take(3).len() + s.len() should be 8, not 6 (#2148)",
    );
}

/// REGRESSION: subrange(0, n) must not corrupt source sequence length.
///
/// The #2494 zero-offset fast path initially returned the source array term
/// directly and overwrote its term-keyed metadata with the shorter length,
/// so later `s.len()` reads saw the subrange length instead of the source.
#[test]
fn test_seq_subrange_zero_offset_preserves_source_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "subrange_vs_source",
        "s.subrange(0, 3).len() + s.len() == 8",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s.subrange(0, 3).len() + s.len() should be 8, not 6 (#2494)",
    );
}

// ========================================================================
// Push overflow guard (#2142)
// ========================================================================

/// REGRESSION: push on max-length sequence must not produce negative length.
///
/// When s.len() == 2^31 - 1 (MAX_I32), push increments to 2^31 which wraps
/// to a negative number in signed BV32. The overflow guard
/// (`assert new_len >= old_len`) makes the context unsatisfiable, so
/// any assertion that depends on the push result cannot verify.
///
/// Without the overflow guard, `s.push(42).len() >= 0` would verify
/// despite the length wrapping to zero.
/// Fixes #2142, updated for unsigned BV(pointer_width) (#1745).
#[test]
fn test_seq_push_max_length_overflow_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    // Set length to MAX unsigned pointer_width value.
    // On 64-bit: 18446744073709551615 (u64::MAX).
    ctx.push_obligation(ProofObligation::assume(
        "max_len",
        "s.len() == 18446744073709551615",
    ));
    // Push makes new_len = u64::MAX + 1 = 0 (unsigned BV64 wraps).
    // The overflow guard (new_len >= old_len) is FALSE (0 < u64::MAX),
    // making the context UNSAT. Therefore even an obviously true property
    // about the push result cannot verify.
    ctx.push_obligation(ProofObligation::assert(
        "push_len_nonneg",
        "s.push(42).len() >= 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "push on max-length seq should NOT verify — overflow guard must reject",
    );
}
