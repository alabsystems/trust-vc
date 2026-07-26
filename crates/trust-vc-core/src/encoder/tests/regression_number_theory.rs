// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn gcd_base_case() {
    // gcd(a, 0) = a
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 12"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "gcd_def",
        "result == if b == 0 { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_12", "result == 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gcd(12, 0) = 12");
}

#[test]
fn gcd_one_step() {
    // gcd(12, 8): 12 mod 8 = 4, then gcd(8, 4): 8 mod 4 = 0, result = 4
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "r1", "a1", "b1", "r2", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 12"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 8"));
    ctx.push_obligation(ProofObligation::assume("r1_def", "r1 == a % b"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == b"));
    ctx.push_obligation(ProofObligation::assume("b1_def", "b1 == r1"));
    ctx.push_obligation(ProofObligation::assume("r2_def", "r2 == a1 % b1"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if r2 == 0 { b1 } else { r2 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "result == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "gcd(12, 8) = 4");
}

#[test]
fn lcm_from_gcd() {
    // lcm(a, b) = a * b / gcd(a, b) = 12 * 8 / 4 = 24
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "gcd", "product", "lcm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 12"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 8"));
    ctx.push_obligation(ProofObligation::assume("gcd_val", "gcd == 4"));
    ctx.push_obligation(ProofObligation::assume("prod_def", "product == a * b"));
    ctx.push_obligation(ProofObligation::assume("lcm_def", "lcm == product / gcd"));
    ctx.push_obligation(ProofObligation::assert("is_24", "lcm == 24"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "lcm(12, 8) = 24");
}

#[test]
fn coprime_gcd_one() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "gcd"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 11"));
    ctx.push_obligation(ProofObligation::assume("gcd_val", "gcd == 1"));
    ctx.push_obligation(ProofObligation::assert("coprime", "gcd == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gcd(7, 11) = 1 (coprime)");
}

#[test]
fn divisibility_check() {
    let mut ctx = VerificationContext::new();
    for v in &["n", "d", "remainder"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("divides", i32_ty());
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 15"));
    ctx.push_obligation(ProofObligation::assume("d_val", "d == 5"));
    ctx.push_obligation(ProofObligation::assume("rem_def", "remainder == n % d"));
    ctx.push_obligation(ProofObligation::assume(
        "div_def",
        "divides == if remainder == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "five_divides_fifteen",
        "divides == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "5 divides 15");
}

#[test]
fn modular_addition() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "m", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 8"));
    ctx.push_obligation(ProofObligation::assume("m_val", "m == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == (a + b) % m",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "result == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(7 + 8) mod 10 = 5");
}

#[test]
fn even_odd_parity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", u32_ty());
    ctx.declare_var_typed("is_even", i32_ty());
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 14"));
    ctx.push_obligation(ProofObligation::assume(
        "even_def",
        "is_even == if n % 2 == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fourteen_even", "is_even == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "14 is even");
}

#[test]
fn sum_first_n() {
    // 1 + 2 + ... + n = n*(n+1)/2
    let mut ctx = VerificationContext::new();
    for v in &["n", "sum", "formula"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 10"));
    ctx.push_obligation(ProofObligation::assume("sum_val", "sum == 55"));
    ctx.push_obligation(ProofObligation::assume(
        "formula_def",
        "formula == n * (n + 1) / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("matches", "sum == formula"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "sum(1..10) = 55 = 10*11/2");
}

#[test]
fn perfect_square_check() {
    let mut ctx = VerificationContext::new();
    for v in &["n", "root", "square"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 49"));
    ctx.push_obligation(ProofObligation::assume("root_val", "root == 7"));
    ctx.push_obligation(ProofObligation::assume("sq_def", "square == root * root"));
    ctx.push_obligation(ProofObligation::assert("is_perfect", "square == n"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "49 = 7^2 (perfect square)");
}

#[test]
fn fibonacci_pair() {
    let mut ctx = VerificationContext::new();
    for v in &["f5", "f6", "f7"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("f5_val", "f5 == 5"));
    ctx.push_obligation(ProofObligation::assume("f6_val", "f6 == 8"));
    ctx.push_obligation(ProofObligation::assume("f7_def", "f7 == f5 + f6"));
    ctx.push_obligation(ProofObligation::assert("is_13", "f7 == 13"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fib: 5 + 8 = 13");
}
