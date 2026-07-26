// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn tokens_decrease_on_request() {
    let mut ctx = VerificationContext::new();
    for v in &["tokens", "cost", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 100"));
    ctx.push_obligation(ProofObligation::assume("c", "cost == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == tokens - cost",
    ));
    ctx.push_obligation(ProofObligation::assert("is_99", "remaining == 99"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 tokens - 1 cost = 99 remaining");
}

#[test]
fn reject_when_no_tokens() {
    let mut ctx = VerificationContext::new();
    for v in &["tokens", "cost"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("allowed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 0"));
    ctx.push_obligation(ProofObligation::assume("c", "cost == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "allowed == if tokens >= cost { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rejected", "allowed == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 tokens < 1 cost → rejected");
}

#[test]
fn refill_adds_tokens() {
    let mut ctx = VerificationContext::new();
    for v in &["tokens", "refill_amount", "capacity", "new_tokens"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 50"));
    ctx.push_obligation(ProofObligation::assume("ra", "refill_amount == 10"));
    ctx.push_obligation(ProofObligation::assume("cap", "capacity == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_tokens == if tokens + refill_amount > capacity { capacity } else { tokens + refill_amount }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_60", "new_tokens == 60"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refill: 50 + 10 = 60 (under cap)");
}

#[test]
fn refill_capped_at_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["tokens", "refill_amount", "capacity", "new_tokens"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 95"));
    ctx.push_obligation(ProofObligation::assume("ra", "refill_amount == 10"));
    ctx.push_obligation(ProofObligation::assume("cap", "capacity == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_tokens == if tokens + refill_amount > capacity { capacity } else { tokens + refill_amount }",
    ));
    ctx.push_obligation(ProofObligation::assert("capped", "new_tokens == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refill: 95 + 10 = 105 → capped at 100");
}

#[test]
fn sliding_window_count() {
    let mut ctx = VerificationContext::new();
    for v in &["requests_in_window", "limit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("over_limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("riw", "requests_in_window == 150"));
    ctx.push_obligation(ProofObligation::assume("l", "limit == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ol_def",
        "over_limit == if requests_in_window > limit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("over", "over_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "150 requests > 100 limit → over limit");
}

#[test]
fn burst_allowance() {
    // Allow bursts up to burst_size above steady rate
    let mut ctx = VerificationContext::new();
    for v in &["steady_rate", "burst_size", "max_burst"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sr", "steady_rate == 10"));
    ctx.push_obligation(ProofObligation::assume("bs", "burst_size == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "mb_def",
        "max_burst == steady_rate + burst_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "max_burst == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max burst: 10 steady + 5 burst = 15");
}

#[test]
fn exponential_backoff_delay() {
    let mut ctx = VerificationContext::new();
    for v in &["base_ms", "attempt", "delay_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bm", "base_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("a", "attempt == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "dm_def",
        "delay_ms == base_ms << attempt",
    ));
    // 100 << 3 = 800
    ctx.push_obligation(ProofObligation::assert("is_800", "delay_ms == 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "backoff: 100ms << 3 = 800ms");
}

#[test]
fn per_client_quota() {
    let mut ctx = VerificationContext::new();
    for v in &["total_capacity", "num_clients", "per_client"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tc", "total_capacity == 1000"));
    ctx.push_obligation(ProofObligation::assume("nc", "num_clients == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "pc_def",
        "per_client == total_capacity / num_clients",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "per_client == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "1000 / 10 clients = 100 per client");
}

#[test]
fn cooldown_period() {
    // After hitting limit, wait cooldown before accepting
    let mut ctx = VerificationContext::new();
    for v in &["time_since_limit", "cooldown"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_accept", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tsl", "time_since_limit == 60"));
    ctx.push_obligation(ProofObligation::assume("cd", "cooldown == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "can_accept == if time_since_limit >= cooldown { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("accept", "can_accept == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "60s >= 30s cooldown → can accept");
}

#[test]
fn weighted_request_cost() {
    // Different request types have different costs
    let mut ctx = VerificationContext::new();
    for v in &["tokens", "read_cost", "write_cost", "after_write"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 100"));
    ctx.push_obligation(ProofObligation::assume("rc", "read_cost == 1"));
    ctx.push_obligation(ProofObligation::assume("wc", "write_cost == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "aw_def",
        "after_write == tokens - write_cost",
    ));
    ctx.push_obligation(ProofObligation::assert("is_95", "after_write == 95"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "write costs 5: 100 - 5 = 95");
}
