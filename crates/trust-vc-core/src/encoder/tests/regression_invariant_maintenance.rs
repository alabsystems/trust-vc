// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn counter_invariant_inc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("c", u32_ty());
    ctx.declare_var_typed("next", u32_ty());
    ctx.push_obligation(ProofObligation::assume("c_bounds", "c >= 0 && c < 100"));
    ctx.push_obligation(ProofObligation::assume("next_inc", "next == c + 1"));
    ctx.push_obligation(ProofObligation::assert(
        "next_bounds",
        "next >= 0 && next <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "increment should preserve the bounded counter invariant",
    );
}

#[test]
fn counter_invariant_dec() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("c", u32_ty());
    ctx.declare_var_typed("next", u32_ty());
    ctx.push_obligation(ProofObligation::assume("c_bounds", "c > 0 && c <= 100"));
    ctx.push_obligation(ProofObligation::assume("next_dec", "next == c - 1"));
    ctx.push_obligation(ProofObligation::assert(
        "next_bounds",
        "next >= 0 && next < 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "decrement should preserve the bounded counter invariant",
    );
}

#[test]
fn bounded_sum_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("s", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_bounds", "a >= 0 && a <= 50"));
    ctx.push_obligation(ProofObligation::assume("b_bounds", "b >= 0 && b <= 50"));
    ctx.push_obligation(ProofObligation::assume("s_sum", "s == a + b"));
    ctx.push_obligation(ProofObligation::assert("s_bounds", "s >= 0 && s <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bounded nonnegative sums should stay within the invariant",
    );
}

#[test]
fn nonneg_preserved_by_add() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.declare_var_typed("z", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_bounds", "x >= 0 && x <= 500"));
    ctx.push_obligation(ProofObligation::assume("y_bounds", "y >= 0 && y <= 500"));
    ctx.push_obligation(ProofObligation::assume("z_sum", "z == x + y"));
    ctx.push_obligation(ProofObligation::assert("z_nonnegative", "z >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "adding nonnegative bounded values should stay nonnegative",
    );
}

#[test]
fn range_preserved_by_clamp() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.declare_var_typed("clamped", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "x_bounds",
        "x >= -1000 && x <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("lo_zero", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_hundred", "hi == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "clamp_def",
        "clamped == if x < lo { lo } else { if x > hi { hi } else { x } }",
    ));
    // This explicit arithmetic tactic uses mathematical integers. The input
    // and both endpoints are bounded far inside i32, and the ITE only selects
    // one of those values, so there is no wrapping behavior to abstract away.
    ctx.push_obligation(
        ProofObligation::assert("clamped_bounds", "clamped >= 0 && clamped <= 100")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamp should preserve the target range invariant");

    ctx.push_obligation(ProofObligation::assume("x_at_upper_endpoint", "x == 100"));
    ctx.push_obligation(
        ProofObligation::assert("false_clamped_bound", "clamped < 100")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "the nonlinear tactic must reject a strict bound at the clamp endpoint",
    );
}

#[test]
fn even_plus_two_stays_even() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_bounds", "x >= 0 && x <= 100"));
    ctx.push_obligation(ProofObligation::assume("x_even", "x % 2 == 0"));
    ctx.push_obligation(ProofObligation::assume("y_inc", "y == x + 2"));
    ctx.push_obligation(ProofObligation::assert("y_even", "y % 2 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "adding two to an even value should keep it even");
}

#[test]
fn positive_stays_positive_on_inc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_bounds", "x > 0 && x < 1000"));
    ctx.push_obligation(ProofObligation::assume("y_inc", "y == x + 1"));
    ctx.push_obligation(ProofObligation::assert("y_positive", "y > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "incrementing a positive value should preserve positivity",
    );
}

#[test]
fn ordered_pair_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.declare_var_typed("new_lo", i32_ty());
    ctx.declare_var_typed("new_hi", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo_value", "lo == 5"));
    ctx.push_obligation(ProofObligation::assume("hi_value", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume("new_lo_same", "new_lo == lo"));
    ctx.push_obligation(ProofObligation::assume("new_hi_inc", "new_hi == hi + 1"));
    ctx.push_obligation(ProofObligation::assert("pair_ordered", "new_lo <= new_hi"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "updating the upper bound should preserve ordering");
}

#[test]
fn capacity_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("len", u32_ty());
    ctx.declare_var_typed("cap", u32_ty());
    ctx.declare_var_typed("new_len", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_le_cap", "len <= cap"));
    ctx.push_obligation(ProofObligation::assume("cap_fixed", "cap == 16"));
    ctx.push_obligation(ProofObligation::assume("len_not_full", "len < 16"));
    ctx.push_obligation(ProofObligation::assume("new_len_inc", "new_len == len + 1"));
    ctx.push_obligation(ProofObligation::assert("new_len_le_cap", "new_len <= cap"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "incrementing a non-full length should preserve capacity",
    );
}

#[test]
fn balance_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("balance", i32_ty());
    ctx.declare_var_typed("deposit", i32_ty());
    ctx.declare_var_typed("new_balance", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "balance_bounds",
        "balance >= 0 && balance <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "deposit_bounds",
        "deposit >= 0 && deposit <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "new_balance_sum",
        "new_balance == balance + deposit",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "new_balance_nonnegative",
        "new_balance >= 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nonnegative balances should stay nonnegative after deposits",
    );
}
