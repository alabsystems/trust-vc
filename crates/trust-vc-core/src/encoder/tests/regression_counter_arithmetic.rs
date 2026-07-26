// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn increment_from_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("c0", u32_ty());
    ctx.declare_var_typed("c1", u32_ty());
    ctx.push_obligation(ProofObligation::assume("c0_zero", "c0 == 0"));
    ctx.push_obligation(ProofObligation::assume("c1_inc", "c1 == c0 + 1"));
    ctx.push_obligation(ProofObligation::assert("c1_one", "c1 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "incrementing zero should produce one");
}

#[test]
fn decrement_from_ten() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("c0", u32_ty());
    ctx.declare_var_typed("c1", u32_ty());
    ctx.push_obligation(ProofObligation::assume("c0_ten", "c0 == 10"));
    ctx.push_obligation(ProofObligation::assume("c1_dec", "c1 == c0 - 1"));
    ctx.push_obligation(ProofObligation::assert("c1_nine", "c1 == 9"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decrementing ten should produce nine");
}

#[test]
fn increment_preserves_positivity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("c", u32_ty());
    ctx.declare_var_typed("next", u32_ty());
    ctx.push_obligation(ProofObligation::assume("c_bounds", "c > 0 && c < 1000"));
    ctx.push_obligation(ProofObligation::assume("next_inc", "next == c + 1"));
    ctx.push_obligation(ProofObligation::assert("next_gt_one", "next > 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "incrementing a positive bounded counter stays above one",
    );
}

#[test]
fn double_increment() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("c0", u32_ty());
    ctx.declare_var_typed("c1", u32_ty());
    ctx.declare_var_typed("c2", u32_ty());
    ctx.push_obligation(ProofObligation::assume("c0_five", "c0 == 5"));
    ctx.push_obligation(ProofObligation::assume("c1_inc", "c1 == c0 + 1"));
    ctx.push_obligation(ProofObligation::assume("c2_inc", "c2 == c1 + 1"));
    ctx.push_obligation(ProofObligation::assert("c2_seven", "c2 == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "two increments from five should produce seven");
}

#[test]
fn counter_reset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("c", u32_ty());
    ctx.declare_var_typed("reset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 42"));
    ctx.push_obligation(ProofObligation::assume("reset_zero", "reset == 0"));
    ctx.push_obligation(ProofObligation::assert("reset_lt_c", "reset < c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "resetting a nonzero counter should reduce it to zero",
    );
}

#[test]
fn counter_never_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("c_bounds", "c >= 0 && c <= 100"));
    ctx.push_obligation(ProofObligation::assert("c_nonnegative", "c >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "unsigned counters should remain nonnegative");
}

#[test]
fn counter_modular_wrap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("c", u32_ty());
    ctx.declare_var_typed("next", u32_ty());
    ctx.push_obligation(ProofObligation::assume("c_ten", "c == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "next_mod_inc",
        "next == (c + 1) % 12",
    ));
    ctx.push_obligation(ProofObligation::assert("next_eleven", "next == 11"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "increment modulo twelve should produce eleven from ten",
    );
}

#[test]
fn counter_saturate_at_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("c", u32_ty());
    ctx.declare_var_typed("limit", u32_ty());
    ctx.declare_var_typed("next", u32_ty());
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 999"));
    ctx.push_obligation(ProofObligation::assume("limit_val", "limit == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "next_sat",
        "next == if c + 1 < limit { c + 1 } else { c }",
    ));
    ctx.push_obligation(ProofObligation::assert("next_stays", "next == 999"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "strict-limit saturation should keep the current counter",
    );
}

#[test]
fn counter_distance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("start", u32_ty());
    ctx.declare_var_typed("end", u32_ty());
    ctx.push_obligation(ProofObligation::assume("start_val", "start == 3"));
    ctx.push_obligation(ProofObligation::assume("end_val", "end == 10"));
    ctx.push_obligation(ProofObligation::assert("distance", "end - start == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "distance between three and ten should be seven");
}

#[test]
fn counter_increment_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("c", i32_ty());
    ctx.declare_var_typed("next", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c_bounds", "c >= 0 && c <= 100"));
    ctx.push_obligation(ProofObligation::assume(
        "next_bounds",
        "next >= 0 && next <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("next_inc", "next == c + 1"));
    ctx.push_obligation(ProofObligation::assert(
        "next_range",
        "next >= 1 && next <= 101",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bounded i32 increment should stay within the expected range",
    );
}
