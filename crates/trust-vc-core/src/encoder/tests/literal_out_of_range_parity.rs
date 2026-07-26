//! #2778 diagnostic-parity: `integer literal out of range`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Upstream Verus rejects a suffixed integer literal whose value escapes its
//! declared type's range during AST→VIR conversion
//! (`rust_verify/src/rust_to_vir_expr.rs::check_lit_int`), with the byte-exact
//! message `integer literal out of range <IntRange>`. trust-vc reproduces this
//! at IR-lowering time: a suffixed out-of-range literal yields a fail-closed
//! `Error` verdict whose message contains the upstream substring (so a ported
//! `assert_vir_error_msg` matches). These mirror upstream
//! `integers.rs::{test4_fails, test_literals_fails2..6}`.
//!
//! Controls confirm the soundness boundary: `-128i8` (i8::MIN) is accepted (the
//! negation is folded before the range check), and *unsuffixed* literals are
//! never range-checked against their `Int{32}` placeholder type.

use super::*;
use crate::ir::TrustVcType;

/// Verifies a single all-constant assertion with overflow checks enabled,
/// matching the upstream literal-range test shapes (`255u8 == 256u8 - 1`).
fn verify_cond(cond: &str) -> VerifyResult {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.push_obligation(ProofObligation::assert("lit_range", cond));
    AYEncoder::verify(&ctx)
}

/// `integers.rs::test_literals_fails2`: `256u8` escapes `u8`.
#[test]
fn literal_256u8_out_of_range_is_error() {
    expect_error_containing(
        &verify_cond("255u8 == 256u8 - 1"),
        "integer literal out of range",
        "#2778 integers.rs test_literals_fails2: 256u8 escapes u8",
    );
}

/// `integers.rs::test4_fails`-shape: `300u8` escapes `u8` (300 > 255).
#[test]
fn literal_300u8_out_of_range_is_error() {
    expect_error_containing(
        &verify_cond("300u8 == 44u8"),
        "integer literal out of range",
        "#2778 integers.rs test4_fails: 300 does not fit u8",
    );
}

/// `integers.rs::test_literals_fails4`: `128i8` escapes `i8` (max 127).
#[test]
fn literal_128i8_out_of_range_is_error() {
    expect_error_containing(
        &verify_cond("127i8 == 128i8 - 1"),
        "integer literal out of range",
        "#2778 integers.rs test_literals_fails4: 128i8 escapes i8",
    );
}

/// `integers.rs::test_literals_fails3`: `-129i8` escapes `i8` (min -128). The
/// negation is folded before the range check, so the *negated* value `-129` is
/// what fails — `-128i8` (i8::MIN) must still be accepted (see control below).
#[test]
fn literal_negative_129i8_out_of_range_is_error() {
    expect_error_containing(
        &verify_cond("-128i8 == -129i8 + 1"),
        "integer literal out of range",
        "#2778 integers.rs test_literals_fails3: -129i8 escapes i8",
    );
}

/// Control: `-128i8` is `i8::MIN` and must NOT be rejected as out-of-range,
/// even though the bare inner literal `128i8` would not fit `i8` — the negation
/// is folded before the range check (`in_negative_literal`). Mirrors the
/// passing upstream `integers.rs::test_literals` boundary `-128i8`.
///
/// We assert the literal is *not* turned into an `integer literal out of range`
/// error. (Whether `-128i8 == -127i8 - 1` ultimately verifies under
/// `with_overflow_checks()` is a separate, pre-existing matter: the i8::MIN
/// negation-overflow obligation currently returns Unknown via an ay-dpll CEGQI
/// empty-model artifact, unrelated to this literal-range diagnostic.)
#[test]
fn literal_negative_128i8_min_is_not_out_of_range() {
    // No overflow checks: isolate the literal-range lowering decision from the
    // unrelated i8::MIN negation-overflow solver artifact.
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "min_literal",
        "-128i8 == -127i8 - 1",
    ));
    let result = AYEncoder::verify(&ctx);
    if let VerifyResult::Error { message } = &result {
        assert!(
            !message.contains("integer literal out of range"),
            "-128i8 (i8::MIN) must not be rejected as an out-of-range literal, got: {message}"
        );
    }
    expect_verified(
        &result,
        "#2778 integers.rs test_literals: -128i8 is i8::MIN and must verify without overflow checks",
    );
}

/// Control: an *unsuffixed* large literal (`4294967295`, u32::MAX) must NOT be
/// range-checked against the `Int{32}` placeholder it carries before context
/// coercion. Lowering must keep it; rejecting it would be a false positive that
/// would break the large body of existing wrapping/boundary regression tests.
#[test]
fn unsuffixed_large_literal_not_rejected_at_lowering() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 4294967295"));
    ctx.push_obligation(ProofObligation::assert("ok", "x + 1 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "unsuffixed 4294967295 must lower (not be rejected as out-of-range i32)",
    );
}
