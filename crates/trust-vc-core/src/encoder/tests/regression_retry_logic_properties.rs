// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn retry_count_increments() {
    let mut ctx = VerificationContext::new();
    for v in &["attempt", "next_attempt"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "attempt == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "na_def",
        "next_attempt == attempt + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "next_attempt == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "retry: attempt 2 → 3");
}

#[test]
fn max_retries_exceeded() {
    let mut ctx = VerificationContext::new();
    for v in &["attempt", "max_retries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_stop", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "attempt == 5"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_retries == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ss_def",
        "should_stop == if attempt >= max_retries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("stop", "should_stop == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "attempt 5 >= max 3 → stop retrying");
}

#[test]
fn exponential_backoff_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["base_delay", "attempt", "delay"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bd", "base_delay == 100"));
    ctx.push_obligation(ProofObligation::assume("a", "attempt == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "delay == base_delay << attempt",
    ));
    // 100 << 4 = 1600
    ctx.push_obligation(ProofObligation::assert("is_1600", "delay == 1600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "backoff: 100 << 4 = 1600ms");
}

#[test]
fn jitter_bounds() {
    // Delay with jitter stays in [delay, delay + max_jitter]
    let mut ctx = VerificationContext::new();
    for v in &["delay", "jitter", "max_jitter", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d", "delay == 500"));
    ctx.push_obligation(ProofObligation::assume("j", "jitter == 30")); // random value
    ctx.push_obligation(ProofObligation::assume("mj", "max_jitter == 100"));
    ctx.push_obligation(ProofObligation::assume("t_def", "total == delay + jitter"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "total >= delay && total <= delay + max_jitter",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "530 in [500, 600]");
}

#[test]
fn circuit_breaker_open() {
    let mut ctx = VerificationContext::new();
    for v in &["failure_count", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("circuit_open", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fc", "failure_count == 10"));
    ctx.push_obligation(ProofObligation::assume("th", "threshold == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "circuit_open == if failure_count >= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("open", "circuit_open == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 failures >= threshold 5 → circuit open");
}

#[test]
fn circuit_breaker_half_open() {
    let mut ctx = VerificationContext::new();
    for v in &["time_since_open", "recovery_timeout"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("half_open", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tso", "time_since_open == 60"));
    ctx.push_obligation(ProofObligation::assume("rt", "recovery_timeout == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "half_open == if time_since_open >= recovery_timeout { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_half_open", "half_open == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "60s >= 30s recovery → half-open");
}

#[test]
fn success_resets_failure_count() {
    let mut ctx = VerificationContext::new();
    for v in &["failure_count", "after_success"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fc", "failure_count == 4"));
    ctx.push_obligation(ProofObligation::assume("as_def", "after_success == 0"));
    ctx.push_obligation(ProofObligation::assert("reset", "after_success == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "success resets failure count to 0");
}

#[test]
fn deadline_remaining() {
    let mut ctx = VerificationContext::new();
    for v in &["deadline", "elapsed", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("dl", "deadline == 5000"));
    ctx.push_obligation(ProofObligation::assume("el", "elapsed == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == deadline - elapsed",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2000", "remaining == 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5000 - 3000 = 2000ms remaining");
}

#[test]
fn retry_with_fallback() {
    let mut ctx = VerificationContext::new();
    for v in &["attempt", "max_retries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("use_fallback", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "attempt == 3"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_retries == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "uf_def",
        "use_fallback == if attempt >= max_retries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fallback", "use_fallback == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "attempt 3 >= max 3 → use fallback");
}

#[test]
fn total_wait_time() {
    // 3 retries with delays: 100 + 200 + 400 = 700
    let mut ctx = VerificationContext::new();
    for v in &["d1", "d2", "d3", "total_wait"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d1_val", "d1 == 100"));
    ctx.push_obligation(ProofObligation::assume("d2_val", "d2 == 200"));
    ctx.push_obligation(ProofObligation::assume("d3_val", "d3 == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "tw_def",
        "total_wait == d1 + d2 + d3",
    ));
    ctx.push_obligation(ProofObligation::assert("is_700", "total_wait == 700"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "total wait: 100+200+400 = 700ms");
}
