// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn single_digit_add() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("d1", u32_ty());
    ctx.declare_var_typed("d2", u32_ty());
    ctx.push_obligation(ProofObligation::assume("d1_val", "d1 == 3"));
    ctx.push_obligation(ProofObligation::assume("d2_val", "d2 == 4"));
    ctx.push_obligation(ProofObligation::assert("sum_is_7", "d1 + d2 == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 + 4 = 7 (no carry)");
}

#[test]
fn digit_carry() {
    let mut ctx = VerificationContext::new();
    for v in &["d1", "d2", "sum", "low", "carry"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d1_val", "d1 == 7"));
    ctx.push_obligation(ProofObligation::assume("d2_val", "d2 == 8"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == d1 + d2"));
    ctx.push_obligation(ProofObligation::assume("low_def", "low == sum % 10"));
    ctx.push_obligation(ProofObligation::assume("carry_def", "carry == sum / 10"));
    ctx.push_obligation(ProofObligation::assert("low_is_5", "low == 5"));
    ctx.push_obligation(ProofObligation::assert("carry_is_1", "carry == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "7+8=15: low digit 5, carry 1");
}

#[test]
fn two_digit_no_carry() {
    let mut ctx = VerificationContext::new();
    for v in &["tens1", "ones1", "tens2", "ones2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tens1_val", "tens1 == 2"));
    ctx.push_obligation(ProofObligation::assume("ones1_val", "ones1 == 3"));
    ctx.push_obligation(ProofObligation::assume("tens2_val", "tens2 == 4"));
    ctx.push_obligation(ProofObligation::assume("ones2_val", "ones2 == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "result",
        "ones1 + ones2 == 8 && tens1 + tens2 == 6",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "23 + 45 = 68 (no carry between digits)");
}

#[test]
fn two_digit_with_carry() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "ones1",
        "ones2",
        "raw",
        "carry",
        "lo",
        "tens1",
        "tens2",
        "result_tens",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ones1_val", "ones1 == 7"));
    ctx.push_obligation(ProofObligation::assume("ones2_val", "ones2 == 8"));
    ctx.push_obligation(ProofObligation::assume("raw_def", "raw == ones1 + ones2"));
    ctx.push_obligation(ProofObligation::assume("carry_def", "carry == raw / 10"));
    ctx.push_obligation(ProofObligation::assume("lo_def", "lo == raw % 10"));
    ctx.push_obligation(ProofObligation::assume("tens1_val", "tens1 == 3"));
    ctx.push_obligation(ProofObligation::assume("tens2_val", "tens2 == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "result_tens_def",
        "result_tens == tens1 + tens2 + carry",
    ));
    ctx.push_obligation(ProofObligation::assert("lo_is_5", "lo == 5"));
    ctx.push_obligation(ProofObligation::assert("tens_is_8", "result_tens == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "37 + 48 = 85 (carry from ones)");
}

#[test]
fn chain_carry() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "ab", "ab_lo", "c1", "bc", "bc_lo", "c2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 9"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 9"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 9"));
    ctx.push_obligation(ProofObligation::assume("ab_def", "ab == a + b"));
    ctx.push_obligation(ProofObligation::assume("ab_lo_def", "ab_lo == ab % 10"));
    ctx.push_obligation(ProofObligation::assume("c1_def", "c1 == ab / 10"));
    ctx.push_obligation(ProofObligation::assume("bc_def", "bc == ab_lo + c"));
    ctx.push_obligation(ProofObligation::assume("bc_lo_def", "bc_lo == bc % 10"));
    ctx.push_obligation(ProofObligation::assume("c2_def", "c2 == bc / 10 + c1"));
    ctx.push_obligation(ProofObligation::assert("bc_lo_is_7", "bc_lo == 7"));
    ctx.push_obligation(ProofObligation::assert("c2_is_2", "c2 == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "9+9+9=27: low digit 7, carry 2");
}

#[test]
fn byte_overflow_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("sum", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 200"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 100"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b"));
    ctx.push_obligation(ProofObligation::assert("no_wrap", "sum == 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "200 + 100 = 300 in u32 (no wrapping)");
}

#[test]
fn nibble_add() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("sum", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b"));
    ctx.push_obligation(ProofObligation::assert("fits", "sum == 17 && sum < 256"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 + 7 = 17, fits in a byte");
}

#[test]
fn borrow_subtraction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assert("diff", "a - b == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 - 7 = 3");
}

#[test]
fn hundreds_addition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("sum", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 150"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 250"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b"));
    ctx.push_obligation(ProofObligation::assert("sum_is_400", "sum == 400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "150 + 250 = 400");
}

#[test]
fn power_of_ten_decompose() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "n",
        "hundreds",
        "tens",
        "ones",
        "h_part",
        "t_part",
        "recomposed",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 345"));
    ctx.push_obligation(ProofObligation::assume("hundreds_val", "hundreds == 3"));
    ctx.push_obligation(ProofObligation::assume("tens_val", "tens == 4"));
    ctx.push_obligation(ProofObligation::assume("ones_val", "ones == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "h_part_def",
        "h_part == hundreds * 100",
    ));
    ctx.push_obligation(ProofObligation::assume("t_part_def", "t_part == tens * 10"));
    ctx.push_obligation(ProofObligation::assume(
        "recomposed_def",
        "recomposed == h_part + t_part + ones",
    ));
    ctx.push_obligation(ProofObligation::assert("matches", "recomposed == n"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3*100 + 4*10 + 5 = 345");
}
