// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn addition_associative_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 2"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "addition_associative",
        "(a + b) + c == a + (b + c)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "concrete addition should be associative");
}

#[test]
fn addition_associative_symbolic() {
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
    ctx.push_obligation(ProofObligation::assert(
        "addition_associative",
        "(a + b) + c == a + (b + c)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bounded symbolic addition should be associative");
}

#[test]
fn multiplication_associative_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 2"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "multiplication_associative",
        "(a * b) * c == a * (b * c)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "concrete multiplication associativity may need fallback reasoning",
    );
}

#[test]
fn bitwise_and_associative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0xFF"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0x0F"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 0xF0"));
    ctx.push_obligation(ProofObligation::assert(
        "bitwise_and_associative",
        "(a & b) & c == a & (b & c)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "bitwise AND associativity may need fallback reasoning",
    );
}

#[test]
fn bitwise_or_associative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0xFF"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0x0F"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 0xF0"));
    ctx.push_obligation(ProofObligation::assert(
        "bitwise_or_associative",
        "(a | b) | c == a | (b | c)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "bitwise OR associativity may need fallback reasoning",
    );
}

#[test]
fn bitwise_xor_associative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 12"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "bitwise_xor_associative",
        "(a ^ b) ^ c == a ^ (b ^ c)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "bitwise XOR associativity may need fallback reasoning",
    );
}

#[test]
fn subtraction_not_associative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "subtraction_not_associative",
        "(a - b) - c != a - (b - c)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "subtraction should not be associative for 10, 5, and 2",
    );
}

#[test]
fn addition_four_terms() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.declare_var_typed("d", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_min", "a >= -1000"));
    ctx.push_obligation(ProofObligation::assume("a_max", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assume("b_min", "b >= -1000"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 1000"));
    ctx.push_obligation(ProofObligation::assume("c_min", "c >= -1000"));
    ctx.push_obligation(ProofObligation::assume("c_max", "c <= 1000"));
    ctx.push_obligation(ProofObligation::assume("d_min", "d >= -1000"));
    ctx.push_obligation(ProofObligation::assume("d_max", "d <= 1000"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assume("d_val", "d == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "addition_four_terms",
        "((a + b) + c) + d == a + ((b + c) + d)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "four-term addition regrouping should verify");
}

#[test]
fn max_associative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.declare_var_typed("ab_max", i32_ty());
    ctx.declare_var_typed("bc_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 8"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ab_max_def",
        "ab_max == if a >= b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "bc_max_def",
        "bc_max == if b >= c { b } else { c }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "max_associative",
        "if ab_max >= c { ab_max } else { c } == if a >= bc_max { a } else { bc_max }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max should be associative for concrete inputs");
}

#[test]
fn min_associative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.declare_var_typed("ab_min", i32_ty());
    ctx.declare_var_typed("bc_min", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 8"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ab_min_def",
        "ab_min == if a <= b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "bc_min_def",
        "bc_min == if b <= c { b } else { c }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "min_associative",
        "if ab_min <= c { ab_min } else { c } == if a <= bc_min { a } else { bc_min }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min should be associative for concrete inputs");
}
