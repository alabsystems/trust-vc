// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn index_within_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("idx", u32_ty());
    ctx.declare_var_typed("len", u32_ty());
    ctx.push_obligation(ProofObligation::assume("idx_val", "idx == 3"));
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 10"));
    ctx.push_obligation(ProofObligation::assert("in_bounds", "idx < len"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 < 10");
}

#[test]
fn zero_always_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("len", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 5"));
    ctx.push_obligation(ProofObligation::assert("zero_valid", "0 < len"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 < 5 (first index always valid for non-empty)");
}

#[test]
fn last_index_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("len", u32_ty());
    ctx.declare_var_typed("last", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 8"));
    ctx.push_obligation(ProofObligation::assume("last_def", "last == len - 1"));
    ctx.push_obligation(ProofObligation::assert("last_valid", "last < len"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "len-1 < len for non-empty array");
}

#[test]
fn midpoint_in_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "mid"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 2"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 8"));
    ctx.push_obligation(ProofObligation::assume("lo_le_hi", "lo <= hi"));
    ctx.push_obligation(ProofObligation::assume(
        "mid_def",
        "mid == lo + (hi - lo) / 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mid_bounds",
        "mid >= lo && mid <= hi",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "midpoint between 2 and 8 is in [2,8]");
}

#[test]
fn split_indices_cover() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("len", u32_ty());
    ctx.declare_var_typed("mid", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 10"));
    ctx.push_obligation(ProofObligation::assume("mid_val", "mid == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "cover",
        "mid <= len && len - mid <= len",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "split point 5 covers array of length 10");
}

#[test]
fn stride_in_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["i", "stride", "next", "len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("i_val", "i == 3"));
    ctx.push_obligation(ProofObligation::assume("stride_val", "stride == 2"));
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 10"));
    ctx.push_obligation(ProofObligation::assume("next_def", "next == i + stride"));
    ctx.push_obligation(ProofObligation::assert("next_ok", "next < len"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 + 2 = 5 < 10");
}

#[test]
fn two_indices_ordered() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("i", u32_ty());
    ctx.declare_var_typed("j", u32_ty());
    ctx.declare_var_typed("len", u32_ty());
    ctx.push_obligation(ProofObligation::assume("i_val", "i == 2"));
    ctx.push_obligation(ProofObligation::assume("j_val", "j == 7"));
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "ordered_and_valid",
        "i < j && j < len",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2 < 7 < 10");
}

#[test]
fn offset_from_base() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("base", u32_ty());
    ctx.declare_var_typed("offset", u32_ty());
    ctx.declare_var_typed("idx", u32_ty());
    ctx.declare_var_typed("len", u32_ty());
    ctx.push_obligation(ProofObligation::assume("base_val", "base == 5"));
    ctx.push_obligation(ProofObligation::assume("offset_val", "offset == 3"));
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 20"));
    ctx.push_obligation(ProofObligation::assume("idx_def", "idx == base + offset"));
    ctx.push_obligation(ProofObligation::assert("valid", "idx < len"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5 + 3 = 8 < 20");
}

#[test]
fn slice_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["start", "end_idx", "len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("start_val", "start == 2"));
    ctx.push_obligation(ProofObligation::assume("end_val", "end_idx == 5"));
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "slice_ok",
        "start <= end_idx && end_idx <= len",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "slice [2..5] valid for len=10");
}

#[test]
fn wrap_around_modular() {
    let mut ctx = VerificationContext::new();
    for v in &["idx", "len", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("idx_val", "idx == 7"));
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 5"));
    ctx.push_obligation(ProofObligation::assume("next_def", "next == idx % len"));
    ctx.push_obligation(ProofObligation::assert("in_bounds", "next < len"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "7 % 5 = 2 < 5 (modular wrapping)");
}
