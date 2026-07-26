// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn identity_permutation_fixed_points() {
    // Identity permutation of n elements has n fixed points
    let mut ctx = VerificationContext::new();
    for v in &["n", "fixed_points"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 5"));
    ctx.push_obligation(ProofObligation::assume("fp_def", "fixed_points == n"));
    ctx.push_obligation(ProofObligation::assert("all_fixed", "fixed_points == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "identity has n fixed points");
}

#[test]
fn swap_has_n_minus_2_fixed_points() {
    // Transposition (swap two elements) has n-2 fixed points
    let mut ctx = VerificationContext::new();
    for v in &["n", "fixed_points"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 5"));
    ctx.push_obligation(ProofObligation::assume("fp_def", "fixed_points == n - 2"));
    ctx.push_obligation(ProofObligation::assert("is_3", "fixed_points == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "transposition: 5 - 2 = 3 fixed points");
}

#[test]
fn permutation_composition_length() {
    // Composing permutations of same length gives same length
    let mut ctx = VerificationContext::new();
    for v in &["len_p", "len_q", "len_composed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lp", "len_p == 4"));
    ctx.push_obligation(ProofObligation::assume("lq", "len_q == 4"));
    ctx.push_obligation(ProofObligation::assume("lc_def", "len_composed == len_p"));
    ctx.push_obligation(ProofObligation::assert("same_len", "len_composed == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "composed permutation has same length");
}

#[test]
fn inverse_permutation_exists() {
    // p(i) = j implies p_inv(j) = i
    let mut ctx = VerificationContext::new();
    for v in &["i", "j", "inv_j"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("i_val", "i == 2"));
    ctx.push_obligation(ProofObligation::assume("p_i", "j == 4"));
    ctx.push_obligation(ProofObligation::assume("inv_def", "inv_j == i"));
    ctx.push_obligation(ProofObligation::assert("round_trip", "inv_j == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "p(2)=4, p_inv(4)=2");
}

#[test]
fn cycle_length_divides_order() {
    // A 3-cycle applied 3 times is identity; applied k times has period 3
    let mut ctx = VerificationContext::new();
    for v in &["cycle_len", "applications", "remainder"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cl", "cycle_len == 3"));
    ctx.push_obligation(ProofObligation::assume("apps", "applications == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "rem_def",
        "remainder == applications % cycle_len",
    ));
    ctx.push_obligation(ProofObligation::assert("divides", "remainder == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "6 % 3 = 0 (cycle divides applications)");
}

#[test]
fn derangement_no_fixed_points() {
    // A derangement has 0 fixed points
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fixed_points", u32_ty());
    ctx.declare_var_typed("is_derangement", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fp", "fixed_points == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "der_def",
        "is_derangement == if fixed_points == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_der", "is_derangement == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 fixed points → derangement");
}

#[test]
fn n_factorial_permutations() {
    // 4! = 24 permutations of 4 elements
    let mut ctx = VerificationContext::new();
    for v in &["n", "count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 4"));
    ctx.push_obligation(ProofObligation::assume("count_val", "count == 24"));
    ctx.push_obligation(ProofObligation::assert("is_24", "count == 24"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "4! = 24");
}

#[test]
fn adjacent_transposition_count() {
    // Bubble sort of [3,1,2] needs inversions = 2 adjacent swaps
    let mut ctx = VerificationContext::new();
    for v in &["inversions", "swaps_needed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("inv", "inversions == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "sw_def",
        "swaps_needed == inversions",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "swaps_needed == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2 inversions → 2 adjacent swaps");
}

#[test]
fn even_permutation_parity() {
    // Even number of transpositions → parity 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("transpositions", u32_ty());
    ctx.declare_var_typed("parity", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "transpositions == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "par_def",
        "parity == if transpositions % 2 == 0 { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("even", "parity == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "4 transpositions → even permutation");
}

#[test]
fn permutation_orbit_size() {
    // Element in a k-cycle has orbit size k
    let mut ctx = VerificationContext::new();
    for v in &["cycle_length", "orbit_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cl", "cycle_length == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "os_def",
        "orbit_size == cycle_length",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "orbit_size == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5-cycle → orbit size 5");
}
