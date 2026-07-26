// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn checkout_decreases_available() {
    let mut ctx = VerificationContext::new();
    for v in &["available", "after_checkout"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "available == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ac_def",
        "after_checkout == available - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_9", "after_checkout == 9"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "checkout: 10 → 9 available");
}

#[test]
fn checkin_increases_available() {
    let mut ctx = VerificationContext::new();
    for v in &["available", "after_checkin"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "available == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "aci_def",
        "after_checkin == available + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "after_checkin == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "checkin: 5 → 6 available");
}

#[test]
fn pool_size_invariant() {
    // available + in_use == total
    let mut ctx = VerificationContext::new();
    for v in &["available", "in_use", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "available == 7"));
    ctx.push_obligation(ProofObligation::assume("iu", "in_use == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total == available + in_use",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "total == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pool: 7 available + 3 in use = 10 total");
}

#[test]
fn reject_when_exhausted() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("available", u32_ty());
    ctx.declare_var_typed("can_checkout", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "available == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "cc_def",
        "can_checkout == if available > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rejected", "can_checkout == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 available → checkout rejected");
}

#[test]
fn max_pool_size_enforced() {
    let mut ctx = VerificationContext::new();
    for v in &["current_size", "max_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_grow", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cs", "current_size == 20"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_size == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "cg_def",
        "can_grow == if current_size < max_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no_grow", "can_grow == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "20 == max 20 → cannot grow");
}

#[test]
fn idle_timeout_eviction() {
    let mut ctx = VerificationContext::new();
    for v in &["idle_time", "timeout"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_evict", i32_ty());
    ctx.push_obligation(ProofObligation::assume("it", "idle_time == 300"));
    ctx.push_obligation(ProofObligation::assume("to", "timeout == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "se_def",
        "should_evict == if idle_time > timeout { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("evict", "should_evict == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "idle 300s > timeout 60s → evict");
}

#[test]
fn health_check_valid_connection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ping_ok", i32_ty());
    ctx.declare_var_typed("conn_valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("po", "ping_ok == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cv_def",
        "conn_valid == if ping_ok == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "conn_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ping ok → connection valid");
}

#[test]
fn warmup_creates_min_connections() {
    let mut ctx = VerificationContext::new();
    for v in &["min_size", "created"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ms", "min_size == 5"));
    ctx.push_obligation(ProofObligation::assume("c_def", "created == min_size"));
    ctx.push_obligation(ProofObligation::assert("is_5", "created == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "warmup creates 5 min connections");
}

#[test]
fn checkout_checkin_cycle_preserves() {
    let mut ctx = VerificationContext::new();
    for v in &["initial", "after_checkout", "after_checkin"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("i", "initial == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "aco_def",
        "after_checkout == initial - 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "aci_def",
        "after_checkin == after_checkout + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "preserved",
        "after_checkin == initial",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "checkout+checkin: 8 → 7 → 8");
}

#[test]
fn load_balancing_round_robin() {
    let mut ctx = VerificationContext::new();
    for v in &["current_index", "pool_count", "next_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ci", "current_index == 4"));
    ctx.push_obligation(ProofObligation::assume("pc", "pool_count == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ni_def",
        "next_index == if current_index + 1 >= pool_count { 0 } else { current_index + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "next_index == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "round robin: index 4 of 5 → wraps to 0");
}
