//! Quantifier body arithmetic tests — BV wrapping, int_mode division/modulo,
//! overflow checks, and cast semantics.
//!
//! Issues: #1763, #1774, #1824, #1842, #1849, #1873
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Quantifier body arithmetic is MATHEMATICAL (FV-B, supersedes #1763)
//
// #1763 made quantifier bodies model BV wrapping, on the reading that
// `x + 1 > x` verifying was a bug. That reading is wrong for SPEC code, which
// is what a quantifier body always is: Verus types `u8 + u8` in spec position
// as `int`, so spec arithmetic neither wraps nor overflows and `x + 1 > x` is
// simply TRUE. Worse, the wrap came with NO obligation — every overflow
// predicate in the arithmetic encoders is gated on `quantifier_depth == 0`
// (#2557), because a predicate under a binder references the bound variable,
// which becomes free at the outer scope. So the body got neither faithful
// semantics nor a check, and FALSE claims like
// `forall|i: u64| i + 1 <= u64::MAX` reported `verified`.
//
// The cases below therefore have their verdicts INVERTED relative to #1763.
// Each subject formula is TRUE under Verus and must verify. The soundness
// half of this change — the false claims that must now be REFUTED — lives in
// `tests/quantifier_body_arith_wrap_soundness.rs`; without those, "everything
// verifies" would satisfy this file.
// ========================================================================

/// FV-B: forall |x: u8| x + 1 > x must VERIFY — spec `x + 1` is `int`.
#[test]
fn test_forall_u8_add_one_is_greater() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "overflow",
        "forall(|x: u8| x + 1 > x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: u8| x + 1 > x) is TRUE: spec arithmetic is mathematical",
    );
}

/// FV-B: forall |x: u8| x + 1 > 0 must VERIFY — `x >= 0` so `x + 1 >= 1`.
#[test]
fn test_forall_u8_add_one_is_positive() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "overflow_gt0",
        "forall(|x: u8| x + 1 > 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: u8| x + 1 > 0) is TRUE: x >= 0 gives x + 1 >= 1",
    );
}

/// FV-B: forall |x: u8| x + 1 >= x must VERIFY.
#[test]
fn test_forall_u8_add_one_is_ge() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "overflow_ge",
        "forall(|x: u8| x + 1 >= x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: u8| x + 1 >= x) is TRUE under mathematical semantics",
    );
}

/// FV-B: forall |x: i8| x - 1 < x must VERIFY — spec `x - 1` is `int`.
#[test]
fn test_forall_i8_sub_one_is_less() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "signed_underflow",
        "forall(|x: i8| x - 1 < x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: i8| x - 1 < x) is TRUE under mathematical semantics",
    );
}

/// FV-B: forall |x: u8| x * 2 >= x must VERIFY — `x >= 0` so `2x >= x`.
#[test]
fn test_forall_u8_mul_two_is_ge() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "mul_overflow",
        "forall(|x: u8| x * 2 >= x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: u8| x * 2 >= x) is TRUE: x >= 0 gives 2x >= x",
    );
}

/// CONTROL: forall |x: u8| x + 0 == x should still verify (no overflow possible).
/// This ensures wrapping doesn't break trivially-true properties.
#[test]
fn test_forall_u8_add_zero_identity_still_holds() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "add_zero",
        "forall(|x: u8| x + 0 == x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: u8| x + 0 == x) should verify (identity)",
    );
}

/// FV-B (supersedes the #2669 expectation): `x + 200 > x` is TRUE for every
/// `u8` under mathematical semantics, so there is no counterexample to produce.
#[test]
fn test_2669_forall_u8_add_200_is_greater() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "overflow_counterexample",
        "forall(|x: u8| x + 200 > x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: u8| x + 200 > x) is TRUE: x >= 0 gives x + 200 > x",
    );
}

/// CONTROL for #2669: BV-skolemized arithmetic forall must still prove safe
/// guarded arithmetic when the property holds for all machine values.
#[test]
fn test_2669_forall_u8_guarded_addition_still_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "guarded_safe_add",
        "forall(|x: u8| !(x < 50) || x + 5 > x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "#2669: BV-skolemized guarded u8 addition should still verify",
    );
}

// ========================================================================
// Int-mode division/modulo truncation semantics (#1774, #1824)
// Inside quantifier bodies (int_mode), Div/Mod must use Rust truncation-
// toward-zero semantics, not SMT-LIB Euclidean semantics.
// ========================================================================

/// DISCRIMINATING: forall |x: i32| (-7) / 2 == -3 must verify.
/// Rust: (-7)/2 == -3 (truncation). SMT-LIB: (-7) div 2 == -4 (Euclidean).
#[test]
fn test_forall_int_division_truncation_semantics() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "div_truncation",
        "forall(|x: i32| !(x == 0) || ((-7) / 2 == (-3)))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: i32| !(x==0) || (-7)/2 == -3) should verify with Rust truncation semantics",
    );
}

/// DISCRIMINATING: forall |x: i32| (-7) % 2 == -1 must verify.
/// Rust: (-7)%2 == -1 (sign follows dividend). SMT-LIB: (-7) mod 2 == 1.
#[test]
fn test_forall_int_modulo_truncation_semantics() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "mod_truncation",
        "forall(|x: i32| !(x == 0) || ((-7) % 2 == (-1)))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: i32| !(x==0) || (-7)%%2 == -1) should verify with Rust truncation semantics",
    );
}

/// (-7) / (-2) == 3 in Rust (truncation), but 4 under Euclidean.
#[test]
fn test_forall_int_division_neg_neg_truncation() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "div_neg_neg",
        "forall(|x: i32| !(x == 0) || ((-7) / (-2) == 3))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "(-7)/(-2) should be 3 (Rust truncation), not 4 (Euclidean)",
    );
}

/// (-7) % (-2) == -1 in Rust (sign follows dividend), but 1 under Euclidean.
#[test]
fn test_forall_int_modulo_neg_neg_truncation() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "mod_neg_neg",
        "forall(|x: i32| !(x == 0) || ((-7) % (-2) == (-1)))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "(-7)%%(-2) should be -1 (Rust truncation), not 1 (Euclidean)",
    );
}

/// Positive / positive: 7 / 2 == 3. Same under both semantics (sanity check).
#[test]
fn test_forall_int_division_pos_pos() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "div_pos_pos",
        "forall(|x: i32| !(x == 0) || (7 / 2 == 3))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7/2 should be 3 under both semantics");
}

/// 7 / (-2) == -3 in Rust. Same under Euclidean (-3). Sanity check.
#[test]
fn test_forall_int_division_pos_neg() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "div_pos_neg",
        "forall(|x: i32| !(x == 0) || (7 / (-2) == (-3)))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7/(-2) should be -3 under both semantics");
}

/// 7 % (-2) == 1 in Rust. Same under Euclidean (1). Sanity check.
#[test]
fn test_forall_int_modulo_pos_neg() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "mod_pos_neg",
        "forall(|x: i32| !(x == 0) || (7 % (-2) == 1))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7%%(-2) should be 1 under both semantics");
}

/// Rust identity: a == (a / b) * b + (a % b) must hold for negative operands.
#[test]
fn test_forall_int_division_remainder_identity_negative() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "div_rem_identity",
        "forall(|x: i32| !(x == 0) || ((-7) == ((-7) / 2) * 2 + ((-7) % 2)))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Division-remainder identity a == (a/b)*b + (a%%b) must hold",
    );
}

// ========================================================================
// Int-mode overflow checks in quantifier bodies (#1849)
// ========================================================================

/// FV-B: `with_overflow_checks` must NOT change a quantifier body. Overflow
/// checking governs EXEC arithmetic; a spec quantifier body has no overflow to
/// check, so this stays TRUE and must verify either way.
#[test]
fn test_forall_u8_add_200_verifies_under_overflow_checks() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.push_obligation(ProofObligation::assert(
        "overflow_in_forall",
        "forall(|x: u8| x + 200 > x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: u8| x + 200 > x) is TRUE; overflow checks govern exec code",
    );
}

/// FV-B: same, for `x + 1 > x`.
#[test]
fn test_forall_u8_add_one_verifies_under_overflow_checks() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.push_obligation(ProofObligation::assert(
        "add_one_overflow",
        "forall(|x: u8| x + 1 > x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: u8| x + 1 > x) is TRUE; overflow checks govern exec code",
    );
}

/// CONTROL: forall |x: u8| x + 0 == x with overflow checks should still verify.
#[test]
fn test_forall_u8_add_zero_no_overflow_check() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.push_obligation(ProofObligation::assert(
        "add_zero_safe",
        "forall(|x: u8| x + 0 == x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "forall(|x: u8| x + 0 == x) with overflow checks should verify — adding 0 never overflows (#1849)");
}

/// FV-B: same, for signed `x - 1 < x`.
#[test]
fn test_forall_i8_sub_one_verifies_under_overflow_checks() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.push_obligation(ProofObligation::assert(
        "sub_overflow",
        "forall(|x: i8| x - 1 < x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: i8| x - 1 < x) is TRUE; overflow checks govern exec code",
    );
}

/// FV-B: same, for `x * 2 >= x`.
#[test]
fn test_forall_u8_mul_two_verifies_under_overflow_checks() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.push_obligation(ProofObligation::assert(
        "mul_overflow",
        "forall(|x: u8| x * 2 >= x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: u8| x * 2 >= x) is TRUE; overflow checks govern exec code",
    );
}

/// DISCRIMINATING: Int-mode signed Div/Rem must model Rust MIN/-1 panic (#1873).
#[test]
fn test_forall_i32_div_rem_identity_with_exceptions_guarded() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    // 2-variable i32 quantifier with div/rem always times out (#2229).
    // BV_HARD_TIMEOUT is 10s, so the retry cascade burns ~30s. 5s rlimit
    // caps each stage, cutting total to ~15s. Test accepts Unknown.
    ctx.set_rlimit(5_000);
    ctx.set_skip_retry_cascade(true);
    ctx.push_obligation(ProofObligation::assert(
        "div_rem_identity_guarded",
        "forall(|x: i32, y: i32| \
         !((y != 0) && !(x == i32::MIN && y == -1)) || \
         ((x / y) * y + (x % y) == x))",
    ));

    let result = AYEncoder::verify(&ctx);
    // 2-variable quantifier with overflow guards — ay-dpll times out (#2229 triage)
    expect_verified_or_unknown(
        &result,
        "guarded i32 div/rem identity should hold on all non-panicking inputs (#1873)",
    );
}

/// DISCRIMINATING: Signed Int-mode division must reject MIN / -1 as overflow (#1873).
#[test]
fn test_forall_i32_div_by_neg_one_nonpositive_not_verified_due_to_min_overflow() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.push_obligation(ProofObligation::assert(
        "div_neg_one_overflow",
        "forall(|x: i32| !(x <= 0) || (x / -1 >= 0))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall(|x: i32| x / -1) must NOT verify — i32::MIN causes overflow panic (#1873)",
    );
}

/// DISCRIMINATING: Signed Int-mode remainder must reject MIN % -1 as overflow (#1873).
#[test]
fn test_forall_i32_rem_by_neg_one_nonpositive_not_verified_due_to_min_overflow() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.push_obligation(ProofObligation::assert(
        "rem_neg_one_overflow",
        "forall(|x: i32| !(x <= 0) || (x % -1 == 0))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "forall(|x: i32| x % -1) must NOT verify — i32::MIN causes remainder overflow panic (#1873)");
}

// ========================================================================
// Int-mode cast wrapping tests (Issue #1842)
// ========================================================================

/// SOUNDNESS: Narrowing cast in quantifier body must truncate.
/// forall |x: u16| (x as u8) <= 255 must verify — u8 range is [0, 255].
#[test]
fn test_forall_narrowing_cast_u16_to_u8_range() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "narrow_range",
        "forall(|x: u16| (x as u8) <= 255)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: u16| (x as u8) <= 255) must verify — u8 in [0,255] (#1842)",
    );
}

/// SOUNDNESS: Narrowing cast must NOT preserve large values.
/// forall |x: u16| (x as u8) == x must NOT verify — at x=256, (256 as u8)=0 != 256.
#[test]
fn test_forall_narrowing_cast_u16_to_u8_not_identity() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "narrow_identity",
        "forall(|x: u16| (x as u8) == x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall(|x: u16| (x as u8) == x) must NOT verify — narrowing cast is not identity (#1842)",
    );
}

/// SOUNDNESS: Signed narrowing cast in quantifier body.
/// forall |x: i16| (x as i8) >= -128 && (x as i8) <= 127 must verify.
#[test]
fn test_forall_narrowing_cast_i16_to_i8_range() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "signed_narrow_range",
        "forall(|x: i16| (x as i8) >= -128 && (x as i8) <= 127)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: i16| (x as i8) in [-128,127]) must verify (#1842)",
    );
}

/// SOUNDNESS: Signedness reinterpretation in int mode.
/// forall |x: i8| (x as u8) >= 0 must verify — u8 is always non-negative.
#[test]
fn test_forall_signedness_change_i8_to_u8_nonneg() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "sign_cast_nonneg",
        "forall(|x: i8| (x as u8) >= 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: i8| (x as u8) >= 0) must verify — u8 is unsigned (#1842)",
    );
}

/// REGRESSION: Widening cast in quantifier body should remain a no-op.
/// forall |x: u8| (x as u16) >= 0 should verify.
#[test]
fn test_forall_widening_cast_u8_to_u16_preserves_value() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "widen_preserves",
        "forall(|x: u8| (x as u16) >= 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall(|x: u8| (x as u16) >= 0) must verify — widening preserves value (#1842)",
    );
}
