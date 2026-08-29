//! End-to-end tests for Int-mode arithmetic overflow detection in quantifier bodies.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Issue #1849: overflow predicates inside quantifier bodies reference
//! bound variables that use Sort::Int (unbounded integers). Collecting
//! these predicates and asserting them at the outer scope constrains
//! the bound variables globally, causing false Verified results.
//!
//! Fix (#2557): overflow predicate collection is suppressed at
//! quantifier_depth > 0.
//!
//! FV-B closes what #2557 left open. #2557 suppressed the OBLIGATION but kept
//! the body's arithmetic WRAPPING, so a quantifier body had neither faithful
//! semantics nor a check and FALSE claims verified. The "future work
//! (Verus-style body precondition encoding)" this file used to promise turned
//! out to be unnecessary: in Verus a quantifier body is SPEC code, where
//! `u8 + u8` has type `int` and cannot overflow at all, so there is no
//! precondition to encode. The bodies below are all mathematically TRUE and
//! now VERIFY; the matching FALSE claims that must still be refuted live in
//! `tests/quantifier_body_arith_wrap_soundness.rs`.
//!
//! Control tests verify overflow detection still works at top level.
//! The unit-level encoder tests live in `int_mode_div_rem_overflow.rs`
//! (div/rem) and `neg_overflow.rs` (negation).

use super::*;

// ========================================================================
// Addition overflow in quantifier bodies (#1849)
// ========================================================================

/// FV-B: `forall(|x: u8| x + 200 > x)` is TRUE — `x >= 0` and spec `+` is
/// mathematical, so no BV8 wrap at `x == 56` exists to refute it.
#[test]
fn test_1849_int_mode_add_in_forall_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "add_overflow",
        "forall(|x: u8| x + 200 > x)",
    ));

    let result = AYEncoder::verify(&ctx);
    // FV-B: the body is mathematical `int` arithmetic, so this is TRUE and the
    // `mod 2^w` NIA terms that used to make it undecidable are gone.
    expect_verified(
        &result,
        "spec quantifier-body arithmetic is mathematical, so this is TRUE",
    );
}

/// CONTROL: u8 addition that cannot overflow SHOULD verify with overflow checks.
///
/// forall(|x: u8| !(x < 50) || x + 5 > x)
/// For x in [0, 49], x + 5 is in [5, 54] — no overflow possible.
/// The guarded implication ensures only safe values are considered.
#[test]
fn test_1849_int_mode_add_safe_in_forall_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "safe_add",
        "forall(|x: u8| !(x < 50) || x + 5 > x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "#1849 control: safe u8 addition in forall should verify — x < 50 guarantees no overflow",
    );
}

// ========================================================================
// Subtraction overflow in quantifier bodies (#1849)
// ========================================================================

/// FV-B: `forall(|x: u32| x - 1 < x)` is TRUE with unbounded integers. The
/// old expectation was a COUNTEREXAMPLE at `x == 0`, manufactured entirely by
/// `wrap_int_to_explicit_range` turning `0 - 1` into `u32::MAX` — precisely
/// the wrap this fix removes. Verus does not wrap spec subtraction.
#[test]
fn test_1849_int_mode_sub_in_forall_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "sub_underflow",
        "forall(|x: u32| x - 1 < x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x - 1 < x holds for every u32 under mathematical semantics",
    );
}

/// CONTROL: u32 subtraction that cannot underflow SHOULD verify.
///
/// forall(|x: u32| !(x > 0) || x - 1 < x)
/// Guard x > 0 ensures x - 1 >= 0, no underflow.
#[test]
fn test_1849_int_mode_sub_safe_in_forall_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "safe_sub",
        "forall(|x: u32| !(x > 0) || x - 1 < x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "#1849 control: safe u32 subtraction in forall should verify — x > 0 guard prevents underflow");
}

// ========================================================================
// Multiplication overflow in quantifier bodies (#1849)
// ========================================================================

/// FV-B: overflow OBLIGATIONS stay suppressed under a binder (#2557), and
/// the body is mathematical, so the true claim below verifies.
///
/// forall(|x: u8| !(x > 1) || x * 200 > x)
/// In int-mode, x * 200 > x is always true for x > 1 (no overflow).
#[test]
fn test_1849_int_mode_mul_in_forall_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mul_overflow",
        "forall(|x: u8| !(x > 1) || x * 200 > x)",
    ));

    let result = AYEncoder::verify(&ctx);
    // FV-B: the body is mathematical `int` arithmetic, so this is TRUE and the
    // `mod 2^w` NIA terms that used to make it undecidable are gone.
    expect_verified(
        &result,
        "spec quantifier-body arithmetic is mathematical, so this is TRUE",
    );
}

/// CONTROL: u8 multiplication that cannot overflow SHOULD verify.
///
/// forall(|x: u8| !(x < 10) || x * 2 >= x)
/// For x in [0, 9], x * 2 is in [0, 18] — no overflow, and x * 2 >= x.
#[test]
fn test_1849_int_mode_mul_safe_in_forall_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "safe_mul",
        "forall(|x: u8| !(x < 10) || x * 2 >= x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "#1849 control: safe u8 multiplication in forall should verify — x < 10 guarantees x*2 < 20 (no overflow)");
}

// ========================================================================
// Signed overflow in quantifier bodies (#1849)
// ========================================================================

/// FV-B: overflow OBLIGATIONS stay suppressed under a binder (#2557), and
/// the body is mathematical, so the true claim below verifies.
///
/// forall(|x: i8| !(x > 0) || x + 127 > 0)
/// In int-mode, x + 127 > 0 is always true for x > 0 (no overflow).
#[test]
fn test_1849_int_mode_signed_add_in_forall_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "signed_add_overflow",
        "forall(|x: i8| !(x > 0) || x + 127 > 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    // FV-B: the body is mathematical `int` arithmetic, so this is TRUE and the
    // `mod 2^w` NIA terms that used to make it undecidable are gone.
    expect_verified(
        &result,
        "spec quantifier-body arithmetic is mathematical, so this is TRUE",
    );
}

/// FV-B: overflow OBLIGATIONS stay suppressed under a binder (#2557), and
/// the body is mathematical, so the true claim below verifies.
///
/// forall(|x: i8| !(x < 0) || x - 1 < 0)
/// In int-mode, x - 1 < 0 is always true for x < 0 (no underflow).
#[test]
fn test_1849_int_mode_signed_sub_in_forall_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "signed_sub_underflow",
        "forall(|x: i8| !(x < 0) || x - 1 < 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    // FV-B: the body is mathematical `int` arithmetic, so this is TRUE and the
    // `mod 2^w` NIA terms that used to make it undecidable are gone.
    expect_verified(
        &result,
        "spec quantifier-body arithmetic is mathematical, so this is TRUE",
    );
}

// ========================================================================
// Negation overflow in quantifier bodies (#2557 audit)
// ========================================================================

/// REGRESSION: i8 negation overflow inside forall must NOT leak overflow
/// predicates to the outer scope.
///
/// forall(|x: i8| -x != x || x == 0)
/// In int-mode, -x != x is true for all x != 0, and x == 0 handles the
/// remaining case. This is a tautology with unbounded integers — and FV-B
/// makes the encoding match that reading, so it now VERIFIES instead of
/// failing closed on `-(-128) == -128`.
///
/// The negation overflow check in logic.rs (int-mode path) collects an
/// overflow predicate that references the quantifier-bound variable x.
/// Without a quantifier_depth guard, this predicate leaks to the outer
/// scope where x is free, causing false counterexamples.
///
/// Part of #2557: negation path needs the same quantifier_depth == 0 guard
/// that was added to add/sub/mul in arith/mod.rs.
#[test]
fn test_2557_int_mode_neg_in_forall_verifies_and_does_not_leak() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "neg_tautology",
        "forall(|x: i8| -x != x || x == 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    // FV-B: the body is mathematical `int` arithmetic, so this is TRUE and the
    // `mod 2^w` NIA terms that used to make it undecidable are gone.
    expect_verified(
        &result,
        "spec quantifier-body arithmetic is mathematical, so this is TRUE",
    );
}
