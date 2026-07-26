// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn modular_bucket_index() {
    let mut ctx = VerificationContext::new();
    for v in &["hash", "num_buckets", "bucket"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hash_val", "hash == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "num_buckets_val",
        "num_buckets == 8",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "bucket_def",
        "bucket == hash % num_buckets",
    ));
    ctx.push_obligation(ProofObligation::assert("bucket_val", "bucket == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "42 % 8 = 2");
}

#[test]
fn bucket_in_range() {
    let mut ctx = VerificationContext::new();
    for v in &["hash", "num_buckets", "bucket"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hash_val", "hash == 12345"));
    ctx.push_obligation(ProofObligation::assume(
        "num_buckets_val",
        "num_buckets == 16",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "bucket_def",
        "bucket == hash % num_buckets",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "bucket < 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "hash % 16 < 16");
}

#[test]
fn power_of_two_bucket_via_mask() {
    let mut ctx = VerificationContext::new();
    for v in &["hash", "bucket"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hash_val", "hash == 42"));
    ctx.push_obligation(ProofObligation::assume("bucket_def", "bucket == hash & 7"));
    ctx.push_obligation(ProofObligation::assert("bucket_val", "bucket == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "42 & 7 = 2 (mod 8 via bitmask)");
}

#[test]
fn different_keys_same_bucket() {
    let mut ctx = VerificationContext::new();
    for v in &["h1", "h2", "b1", "b2", "n"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h1_val", "h1 == 5"));
    ctx.push_obligation(ProofObligation::assume("h2_val", "h2 == 13"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 8"));
    ctx.push_obligation(ProofObligation::assume("b1_def", "b1 == h1 % n"));
    ctx.push_obligation(ProofObligation::assume("b2_def", "b2 == h2 % n"));
    ctx.push_obligation(ProofObligation::assert("collision", "b1 == b2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "5 % 8 == 13 % 8 (both = 5)");
}

#[test]
fn different_keys_different_buckets() {
    let mut ctx = VerificationContext::new();
    for v in &["h1", "h2", "b1", "b2", "n"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h1_val", "h1 == 3"));
    ctx.push_obligation(ProofObligation::assume("h2_val", "h2 == 7"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 8"));
    ctx.push_obligation(ProofObligation::assume("b1_def", "b1 == h1 % n"));
    ctx.push_obligation(ProofObligation::assume("b2_def", "b2 == h2 % n"));
    ctx.push_obligation(ProofObligation::assert("no_collision", "b1 != b2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "3 % 8 != 7 % 8");
}

#[test]
fn xor_hash_combine() {
    let mut ctx = VerificationContext::new();
    for v in &["h1", "h2", "combined"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h1_val", "h1 == 170"));
    ctx.push_obligation(ProofObligation::assume("h2_val", "h2 == 85"));
    ctx.push_obligation(ProofObligation::assume(
        "combined_def",
        "combined == h1 ^ h2",
    ));
    ctx.push_obligation(ProofObligation::assert("combined_val", "combined == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "170 ^ 85 = 255 (0xAA ^ 0x55 = 0xFF)");
}

#[test]
fn xor_hash_self_inverse() {
    let mut ctx = VerificationContext::new();
    for v in &["h", "scrambled", "restored"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h_val", "h == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "scrambled_def",
        "scrambled == h ^ 123",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "restored_def",
        "restored == scrambled ^ 123",
    ));
    ctx.push_obligation(ProofObligation::assert("roundtrip", "restored == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "XOR is self-inverse: (42 ^ 123) ^ 123 = 42");
}

#[test]
fn linear_probe_next() {
    let mut ctx = VerificationContext::new();
    for v in &["bucket", "cap", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bucket_val", "bucket == 7"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == (bucket + 1) % cap",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "next == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "linear probe: (7+1) % 8 = 0");
}

#[test]
fn quadratic_probe_step() {
    let mut ctx = VerificationContext::new();
    for v in &["base", "step", "cap", "probe"] {
        ctx.declare_var_typed(v, u32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= 0 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("base_val", "base == 3"));
    ctx.push_obligation(ProofObligation::assume("step_val", "step == 2"));
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "probe_def",
        "probe == (base + step * step) % cap",
    ));
    ctx.push_obligation(ProofObligation::assert("probe_val", "probe == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "(3 + 2*2) % 16 = 7");
}

#[test]
fn double_hash_combine() {
    let mut ctx = VerificationContext::new();
    for v in &["h1", "h2", "combined"] {
        ctx.declare_var_typed(v, u32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= 0 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("h1_val", "h1 == 100"));
    ctx.push_obligation(ProofObligation::assume("h2_val", "h2 == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "combined_def",
        "combined == h1 + h2",
    ));
    ctx.push_obligation(ProofObligation::assert("sum_combine", "combined == 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "additive hash combine: 100 + 200 = 300");
}
