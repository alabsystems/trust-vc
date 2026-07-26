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
//! quantifier_depth > 0. Int-mode quantifier bodies use unbounded
//! integers where arithmetic cannot overflow — overflow detection
//! requires future work (Verus-style body precondition encoding).
//!
//! Control tests verify overflow detection still works at top level.
//! The unit-level encoder tests live in `int_mode_div_rem_overflow.rs`
//! (div/rem) and `neg_overflow.rs` (negation).

use super::*;

// ========================================================================
// Addition overflow in quantifier bodies (#1849)
// ========================================================================

/// Overflow detection inside forall quantifier bodies is suppressed because
/// overflow predicates reference quantifier-bound variables. Asserting those
/// predicates at the outer scope constrains bound variables globally, causing
/// false Verified results (soundness bug fixed in Part of #2557).
///
/// forall(|x: u8| x + 200 > x)
/// In BV8 semantics, x + 200 wraps at x=56. But in int-mode quantifier
/// bodies (bound variables use Sort::Int), arithmetic is unbounded and
/// x + 200 > x is always true.
///
/// Future work: implement quantifier-body overflow as a body precondition
/// (Verus-style: forall |x: u8| !overflow(x + 200) ==> x + 200 > x).
#[test]
fn test_1849_int_mode_add_overflow_in_forall_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "add_overflow",
        "forall(|x: u8| x + 200 > x)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Modular wrapping inside quantifier bodies creates `mod 2^w` NIA terms
    // that ay-dpll cannot decide. Unknown(incomplete) is acceptable — the
    // critical invariant is no false Counterexample from leaked overflow
    // predicates. Part of #2557, #2668.
    // Modular wrapping inside quantifier bodies creates NIA terms. The solver
    // may find a genuine BV-semantics counterexample (overflow IS possible)
    // or return Unknown(incomplete). Both are sound non-Verified results.
    // Part of #2557, #2668.
    expect_fail_closed(
        &result,
        "#2668: overflow in quantifier body correctly detected or solver inconclusive",
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

/// Overflow detection inside forall quantifier bodies is suppressed (#2557).
/// See test_1849_int_mode_add_overflow_in_forall_not_verified for rationale.
///
/// forall(|x: u32| x - 1 < x)
/// In int-mode, x - 1 < x is always true for pure unbounded integers.
/// However, int-mode quantifier bodies preserve BV wrapping semantics
/// via `wrap_int_to_explicit_range` (modular arithmetic). The solver finds
/// the genuine counterexample at x=0: wrap32(0-1) = u32::MAX, and
/// u32::MAX < 0 is false. This is the correct BV-semantics answer.
///
/// (Contrast with the u8 add/mul tests where the solver's incomplete NIA
/// handling cannot construct counterexamples through `mod 256`.)
#[test]
fn test_1849_int_mode_sub_underflow_in_forall_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "sub_underflow",
        "forall(|x: u32| x - 1 < x)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Solver finds genuine BV-semantics counterexample at x=0 through
    // modular wrapping: wrap32(0-1) = u32::MAX, u32::MAX < 0 is false.
    expect_counterexample(
        &result,
        "#2557: solver correctly finds BV-semantics counterexample via modular wrapping",
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

/// Overflow detection inside forall quantifier bodies is suppressed (#2557).
/// See test_1849_int_mode_add_overflow_in_forall_not_verified for rationale.
///
/// forall(|x: u8| !(x > 1) || x * 200 > x)
/// In int-mode, x * 200 > x is always true for x > 1 (no overflow).
#[test]
fn test_1849_int_mode_mul_overflow_in_forall_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mul_overflow",
        "forall(|x: u8| !(x > 1) || x * 200 > x)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Modular wrapping inside quantifier bodies creates `mod 2^w` NIA terms
    // that ay-dpll cannot decide. Unknown(incomplete) is acceptable — the
    // critical invariant is no false Counterexample. Part of #2668.
    // Modular wrapping inside quantifier bodies creates NIA terms. The solver
    // may find a genuine BV-semantics counterexample (overflow IS possible)
    // or return Unknown(incomplete). Both are sound non-Verified results.
    // Part of #2557, #2668.
    expect_fail_closed(
        &result,
        "#2668: overflow in quantifier body correctly detected or solver inconclusive",
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

/// Overflow detection inside forall quantifier bodies is suppressed (#2557).
/// See test_1849_int_mode_add_overflow_in_forall_not_verified for rationale.
///
/// forall(|x: i8| !(x > 0) || x + 127 > 0)
/// In int-mode, x + 127 > 0 is always true for x > 0 (no overflow).
#[test]
fn test_1849_int_mode_signed_add_overflow_in_forall_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "signed_add_overflow",
        "forall(|x: i8| !(x > 0) || x + 127 > 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Modular wrapping inside quantifier bodies creates `mod 2^w` NIA terms
    // that ay-dpll cannot decide. Unknown(incomplete) is acceptable — the
    // critical invariant is no false Counterexample. Part of #2668.
    // Modular wrapping inside quantifier bodies creates NIA terms. The solver
    // may find a genuine BV-semantics counterexample (overflow IS possible)
    // or return Unknown(incomplete). Both are sound non-Verified results.
    // Part of #2557, #2668.
    expect_fail_closed(
        &result,
        "#2668: overflow in quantifier body correctly detected or solver inconclusive",
    );
}

/// Overflow detection inside forall quantifier bodies is suppressed (#2557).
/// See test_1849_int_mode_add_overflow_in_forall_not_verified for rationale.
///
/// forall(|x: i8| !(x < 0) || x - 1 < 0)
/// In int-mode, x - 1 < 0 is always true for x < 0 (no underflow).
#[test]
fn test_1849_int_mode_signed_sub_underflow_in_forall_not_verified() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "signed_sub_underflow",
        "forall(|x: i8| !(x < 0) || x - 1 < 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Modular wrapping inside quantifier bodies creates `mod 2^w` NIA terms
    // that ay-dpll cannot decide. Unknown(incomplete) is acceptable — the
    // critical invariant is no false Counterexample. Part of #2668.
    // Modular wrapping inside quantifier bodies creates NIA terms. The solver
    // may find a genuine BV-semantics counterexample (overflow IS possible)
    // or return Unknown(incomplete). Both are sound non-Verified results.
    // Part of #2557, #2668.
    expect_fail_closed(
        &result,
        "#2668: overflow in quantifier body correctly detected or solver inconclusive",
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
/// remaining case. This is a tautology with unbounded integers.
///
/// The negation overflow check in logic.rs (int-mode path) collects an
/// overflow predicate that references the quantifier-bound variable x.
/// Without a quantifier_depth guard, this predicate leaks to the outer
/// scope where x is free, causing false counterexamples.
///
/// Part of #2557: negation path needs the same quantifier_depth == 0 guard
/// that was added to add/sub/mul in arith/mod.rs.
#[test]
fn test_2557_int_mode_neg_overflow_in_forall_not_leaked() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("dummy", crate::ir::TrustVcType::parse_or_opaque("i8"));
    ctx.push_obligation(ProofObligation::assume("dummy_val", "dummy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "neg_tautology",
        "forall(|x: i8| -x != x || x == 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Modular wrapping inside quantifier bodies creates `mod 2^w` NIA terms
    // that ay-dpll cannot decide. Unknown(incomplete) is acceptable — the
    // critical invariant is no false Counterexample. Part of #2668.
    // Modular wrapping inside quantifier bodies creates NIA terms. The solver
    // may find a genuine BV-semantics counterexample (overflow IS possible)
    // or return Unknown(incomplete). Both are sound non-Verified results.
    // Part of #2557, #2668.
    expect_fail_closed(
        &result,
        "#2668: overflow in quantifier body correctly detected or solver inconclusive",
    );
}
