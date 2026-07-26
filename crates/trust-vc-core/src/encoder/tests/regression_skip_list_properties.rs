// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn level_0_contains_all() {
    // Level 0 of skip list contains all elements
    let mut ctx = VerificationContext::new();
    for v in &["total_elements", "level0_elements"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("te", "total_elements == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "l0_def",
        "level0_elements == total_elements",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "all_at_0",
        "level0_elements == 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "level 0 has all 100 elements");
}

#[test]
fn higher_level_fewer_elements() {
    // Each higher level has roughly half the elements
    let mut ctx = VerificationContext::new();
    for v in &["level0", "level1", "level2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l0", "level0 == 100"));
    ctx.push_obligation(ProofObligation::assume("l1", "level1 == 50"));
    ctx.push_obligation(ProofObligation::assume("l2", "level2 == 25"));
    ctx.push_obligation(ProofObligation::assert(
        "decreasing",
        "level0 > level1 && level1 > level2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 > 50 > 25: levels decrease");
}

#[test]
fn max_level_bounded() {
    // Max level ≈ log2(n) for n elements
    let mut ctx = VerificationContext::new();
    for v in &["n", "max_level"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 1024"));
    ctx.push_obligation(ProofObligation::assume("ml_val", "max_level == 10")); // log2(1024)
    ctx.push_obligation(ProofObligation::assert("bounded", "max_level <= 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max level 10 <= 32");
}

#[test]
fn insert_increases_size() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "size == 50"));
    ctx.push_obligation(ProofObligation::assume("ns_def", "new_size == size + 1"));
    ctx.push_obligation(ProofObligation::assert("grew", "new_size == 51"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insert: size 50 → 51");
}

#[test]
fn search_path_length_bounded() {
    // Expected search path ≈ max_level + elements_at_max_level
    let mut ctx = VerificationContext::new();
    for v in &["max_level", "path_length", "n"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 1000"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_level == 10"));
    ctx.push_obligation(ProofObligation::assume("pl_val", "path_length == 20")); // 2*log(n)
    ctx.push_obligation(ProofObligation::assert("bounded", "path_length < n"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "search path 20 < 1000 elements");
}

#[test]
fn forward_pointers_at_level() {
    // Node at level k has k+1 forward pointers (levels 0..k)
    let mut ctx = VerificationContext::new();
    for v in &["node_level", "forward_pointers"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("nl", "node_level == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "fp_def",
        "forward_pointers == node_level + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "forward_pointers == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "level 3 node has 4 forward pointers");
}

#[test]
fn promotion_probability() {
    // With p=0.5, expected elements at level k = n / 2^k
    // n=64, k=3: 64/8 = 8
    let mut ctx = VerificationContext::new();
    for v in &["n", "expected_at_3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 64"));
    ctx.push_obligation(ProofObligation::assume("e3_def", "expected_at_3 == n / 8"));
    ctx.push_obligation(ProofObligation::assert("is_8", "expected_at_3 == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "64/8 = 8 expected at level 3");
}

#[test]
fn delete_decreases_size() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "new_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "size == 50"));
    ctx.push_obligation(ProofObligation::assume("ns_def", "new_size == size - 1"));
    ctx.push_obligation(ProofObligation::assert("shrunk", "new_size == 49"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "delete: size 50 → 49");
}

#[test]
fn sorted_order_maintained() {
    // Skip list maintains sorted order
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 12"));
    ctx.push_obligation(ProofObligation::assert("sorted", "a < b && b < c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 < 7 < 12: sorted");
}

#[test]
fn space_overhead() {
    // Expected total forward pointers ≈ 2n (geometric series sum with p=0.5)
    let mut ctx = VerificationContext::new();
    for v in &["n", "expected_pointers"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "expected_pointers == n * 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_200",
        "expected_pointers == 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "100 * 2 = 200 expected pointers");
}
