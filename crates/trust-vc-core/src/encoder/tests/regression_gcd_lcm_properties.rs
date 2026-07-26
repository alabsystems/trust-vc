// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn divisibility_by_self() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 12"));
    ctx.push_obligation(ProofObligation::assert("divides_self", "x % x == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "12 should divide itself");
}

#[test]
fn divisor_of_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 7"));
    ctx.push_obligation(ProofObligation::assert("zero_remainder", "0 % x == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "zero should be divisible by 7");
}

#[test]
fn common_divisor_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 12"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 18"));
    ctx.push_obligation(ProofObligation::assert(
        "common_divisor",
        "a % 6 == 0 && b % 6 == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "6 should divide both 12 and 18");
}

#[test]
fn multiple_of_gcd() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("g", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 12"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 18"));
    ctx.push_obligation(ProofObligation::assume("g_val", "g == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "gcd_divides_both",
        "a % g == 0 && b % g == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "the concrete gcd should divide both values");
}

#[test]
fn lcm_is_multiple() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("lcm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 4"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 6"));
    ctx.push_obligation(ProofObligation::assume("lcm_val", "lcm == 12"));
    ctx.push_obligation(ProofObligation::assert(
        "lcm_multiple",
        "lcm % a == 0 && lcm % b == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "12 should be a common multiple of 4 and 6");
}

#[test]
fn coprime_no_common_factor() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 11"));
    ctx.push_obligation(ProofObligation::assert(
        "no_small_common_factor",
        "a % 2 != 0 && b % 2 != 0 && a % 3 != 0 && b % 3 != 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "7 and 11 should have no common factor 2 or 3");
}

#[test]
fn even_times_any_is_even() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_min", "a >= -1000"));
    ctx.push_obligation(ProofObligation::assume("a_max", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assume("b_min", "b >= -1000"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 1000"));
    ctx.push_obligation(ProofObligation::assume("c_min", "c >= -1000"));
    ctx.push_obligation(ProofObligation::assume("c_max", "c <= 1000"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 6"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == a * b"));
    ctx.push_obligation(ProofObligation::assert("even_product", "c % 2 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "an even number times 5 should stay even");
}

#[test]
fn product_divisible_by_factors() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("p", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("p_val", "p == 15"));
    ctx.push_obligation(ProofObligation::assert(
        "divisible_by_factors",
        "p % a == 0 && p % b == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "15 should be divisible by 3 and 5");
}

#[test]
fn divisibility_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 24"));
    ctx.push_obligation(ProofObligation::assert(
        "many_divisors",
        "a % 2 == 0 && a % 3 == 0 && a % 4 == 0 && a % 6 == 0 && a % 8 == 0 && a % 12 == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "24 should satisfy the concrete divisibility chain");
}

#[test]
fn remainder_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("d", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(ProofObligation::assume("d_val", "d == 7"));
    ctx.push_obligation(ProofObligation::assert("remainder_lt_divisor", "x % d < d"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "the remainder should be smaller than 7");
}
