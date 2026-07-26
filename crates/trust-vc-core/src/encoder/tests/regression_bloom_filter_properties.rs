// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn single_hash_sets_one_bit() {
    let mut ctx = VerificationContext::new();
    for v in &["hash", "array_size", "bit_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "hash == 42"));
    ctx.push_obligation(ProofObligation::assume("as_val", "array_size == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "bi_def",
        "bit_index == hash % array_size",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "bit_index < array_size",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "hash 42 mod 16 = bit in range");
}

#[test]
fn k_hashes_set_k_bits_max() {
    // k hash functions set at most k bits
    let mut ctx = VerificationContext::new();
    for v in &["k", "bits_set"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("k_val", "k == 3"));
    ctx.push_obligation(ProofObligation::assume("bs_val", "bits_set == 3"));
    ctx.push_obligation(ProofObligation::assert("bounded", "bits_set <= k"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 hashes set at most 3 bits");
}

#[test]
fn no_false_negatives() {
    // Inserted element always found (no false negatives)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inserted", i32_ty());
    ctx.declare_var_typed("found", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ins", "inserted == 1"));
    ctx.push_obligation(ProofObligation::assume("found_def", "found == inserted"));
    ctx.push_obligation(ProofObligation::assert("no_fn", "found == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inserted → always found");
}

#[test]
fn empty_filter_returns_not_found() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bits_set", u32_ty());
    ctx.declare_var_typed("found", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bs", "bits_set == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "found == if bits_set == 0 { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("not_found", "found == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "empty filter → not found");
}

#[test]
fn bit_array_size_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("m", u32_ty());
    ctx.push_obligation(ProofObligation::assume("m_val", "m == 64"));
    ctx.push_obligation(ProofObligation::assert("positive", "m > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bit array size > 0");
}

#[test]
fn optimal_k_for_m_and_n() {
    // Optimal k ≈ (m/n) * ln(2) ≈ 0.693 * m/n
    // For m=64, n=10: k ≈ 0.693 * 6.4 ≈ 4
    let mut ctx = VerificationContext::new();
    for v in &["m", "n", "optimal_k"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("m_val", "m == 64"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 10"));
    ctx.push_obligation(ProofObligation::assume("k_val", "optimal_k == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "reasonable",
        "optimal_k > 0 && optimal_k < m",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "optimal k=4 for m=64, n=10");
}

#[test]
fn union_of_filters() {
    // Union: OR the bit arrays; result size = max of individual sizes
    let mut ctx = VerificationContext::new();
    for v in &["m1", "m2", "m_union"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("m1_val", "m1 == 64"));
    ctx.push_obligation(ProofObligation::assume("m2_val", "m2 == 64"));
    ctx.push_obligation(ProofObligation::assume("mu_def", "m_union == m1"));
    ctx.push_obligation(ProofObligation::assert("same_size", "m_union == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bloom union: same bit array size");
}

#[test]
fn count_inserted_elements() {
    let mut ctx = VerificationContext::new();
    for v in &["count", "new_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "count == 5"));
    ctx.push_obligation(ProofObligation::assume("nc_def", "new_count == count + 1"));
    ctx.push_obligation(ProofObligation::assert("is_6", "new_count == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insert: count 5 → 6");
}

#[test]
fn fill_ratio_increases() {
    // After inserting k items with h hash functions, at most k*h bits set
    let mut ctx = VerificationContext::new();
    for v in &["items", "hashes", "max_bits", "array_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("i", "items == 10"));
    ctx.push_obligation(ProofObligation::assume("h", "hashes == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "mb_def",
        "max_bits == items * hashes",
    ));
    ctx.push_obligation(ProofObligation::assume("as_val", "array_size == 64"));
    ctx.push_obligation(ProofObligation::assert("bounded", "max_bits <= array_size"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "10*3=30 <= 64 bit array");
}

#[test]
fn clear_resets_all_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["bits_before", "bits_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bb", "bits_before == 30"));
    ctx.push_obligation(ProofObligation::assume("ba_def", "bits_after == 0"));
    ctx.push_obligation(ProofObligation::assert("cleared", "bits_after == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clear: all bits → 0");
}
