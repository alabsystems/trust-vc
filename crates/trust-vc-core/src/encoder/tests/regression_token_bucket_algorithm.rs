// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn consume_one_token() {
    let mut ctx = VerificationContext::new();
    for v in &["tokens", "new_tokens"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_tokens == tokens - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_9", "new_tokens == 9"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "consume token: 10 → 9");
}

#[test]
fn refill_adds_tokens() {
    let mut ctx = VerificationContext::new();
    for v in &["tokens", "refill_rate", "new_tokens", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 5"));
    ctx.push_obligation(ProofObligation::assume("rr", "refill_rate == 3"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_tokens == if tokens + refill_rate > capacity { capacity } else { tokens + refill_rate }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "new_tokens == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refill: 5 + 3 = 8");
}

#[test]
fn refill_capped_at_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["tokens", "refill_rate", "new_tokens", "capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 9"));
    ctx.push_obligation(ProofObligation::assume("rr", "refill_rate == 5"));
    ctx.push_obligation(ProofObligation::assume("c", "capacity == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_tokens == if tokens + refill_rate > capacity { capacity } else { tokens + refill_rate }",
    ));
    ctx.push_obligation(ProofObligation::assert("capped", "new_tokens == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refill: 9 + 5 capped at 10");
}

#[test]
fn reject_when_no_tokens() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tokens", u32_ty());
    ctx.declare_var_typed("allowed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "allowed == if tokens > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rejected", "allowed == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 tokens → request rejected");
}

#[test]
fn burst_capacity() {
    // Burst = consume all tokens at once
    let mut ctx = VerificationContext::new();
    for v in &["tokens", "burst_size", "new_tokens"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 10"));
    ctx.push_obligation(ProofObligation::assume("bs", "burst_size == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_tokens == tokens - burst_size",
    ));
    ctx.push_obligation(ProofObligation::assert("empty", "new_tokens == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "burst 10: tokens 10 → 0");
}

#[test]
fn multi_token_consume() {
    let mut ctx = VerificationContext::new();
    for v in &["tokens", "cost", "new_tokens"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sufficient", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 7"));
    ctx.push_obligation(ProofObligation::assume("c", "cost == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "suf_def",
        "sufficient == if tokens >= cost { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_tokens == tokens - cost",
    ));
    ctx.push_obligation(ProofObligation::assert("is_sufficient", "sufficient == 1"));
    ctx.push_obligation(ProofObligation::assert("is_4", "new_tokens == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 tokens, cost 3 → sufficient, 4 remaining");
}

#[test]
fn steady_state_rate() {
    // In steady state: consume_rate == refill_rate → tokens stable
    let mut ctx = VerificationContext::new();
    for v in &["tokens", "refill", "consume", "new_tokens"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 5"));
    ctx.push_obligation(ProofObligation::assume("r", "refill == 3"));
    ctx.push_obligation(ProofObligation::assume("c", "consume == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_tokens == tokens + refill - consume",
    ));
    ctx.push_obligation(ProofObligation::assert("stable", "new_tokens == tokens"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "steady state: refill=consume → stable");
}

#[test]
fn tokens_never_negative() {
    // u32 ensures non-negative
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tokens", u32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 0"));
    ctx.push_obligation(ProofObligation::assert("non_neg", "tokens >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32 tokens >= 0");
}

#[test]
fn leaky_bucket_drain() {
    // Leaky bucket: drains at constant rate regardless of input
    let mut ctx = VerificationContext::new();
    for v in &["level", "drain_rate", "new_level"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("l", "level == 8"));
    ctx.push_obligation(ProofObligation::assume("dr", "drain_rate == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "nl_def",
        "new_level == if level >= drain_rate { level - drain_rate } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "new_level == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "leaky bucket: 8 - 2 = 6");
}

#[test]
fn rate_limit_window() {
    // Window-based: count requests in window, reject if > limit
    let mut ctx = VerificationContext::new();
    for v in &["requests_in_window", "limit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("throttled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("riw", "requests_in_window == 100"));
    ctx.push_obligation(ProofObligation::assume("lim", "limit == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "throttled == if requests_in_window > limit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_throttled", "throttled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 > 50 → throttled");
}
