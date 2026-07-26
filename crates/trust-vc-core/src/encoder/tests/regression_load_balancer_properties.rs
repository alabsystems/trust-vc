// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn round_robin_wraps_around() {
    let mut ctx = VerificationContext::new();
    for v in &["current", "num_backends", "next_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "current == 4"));
    ctx.push_obligation(ProofObligation::assume("nb", "num_backends == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "n_def",
        "next_val == if current + 1 >= num_backends { 0 } else { current + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "next_val == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "round robin: 4 of 5 → 0");
}

#[test]
fn weighted_distribution() {
    // Backend with weight 3 gets 3x requests of weight 1
    let mut ctx = VerificationContext::new();
    for v in &["weight_a", "weight_b", "total_weight", "a_share"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("wa", "weight_a == 3"));
    ctx.push_obligation(ProofObligation::assume("wb", "weight_b == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tw_def",
        "total_weight == weight_a + weight_b",
    ));
    ctx.push_obligation(ProofObligation::assume("as_def", "a_share == weight_a"));
    ctx.push_obligation(ProofObligation::assert("a_gets_3", "a_share == 3"));
    ctx.push_obligation(ProofObligation::assert("total_4", "total_weight == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "weighted: A gets 3/4, total weight 4");
}

#[test]
fn least_connections_selects_min() {
    let mut ctx = VerificationContext::new();
    for v in &["conns_a", "conns_b", "conns_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("selected", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ca", "conns_a == 10"));
    ctx.push_obligation(ProofObligation::assume("cb", "conns_b == 3")); // fewest
    ctx.push_obligation(ProofObligation::assume("cc", "conns_c == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "selected == if conns_b <= conns_a && conns_b <= conns_c { conns_b } else { if conns_a <= conns_c { conns_a } else { conns_c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "selected == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "least connections: min(10,3,7) = 3");
}

#[test]
fn health_check_removes_unhealthy() {
    let mut ctx = VerificationContext::new();
    for v in &["total_backends", "unhealthy", "active"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tb", "total_backends == 5"));
    ctx.push_obligation(ProofObligation::assume("uh", "unhealthy == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "active == total_backends - unhealthy",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "active == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5 total - 1 unhealthy = 4 active");
}

#[test]
fn sticky_session_same_backend() {
    let mut ctx = VerificationContext::new();
    for v in &["session_id", "backend_map_result", "expected_backend"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("si", "session_id == 42"));
    ctx.push_obligation(ProofObligation::assume("bmr", "backend_map_result == 3"));
    ctx.push_obligation(ProofObligation::assume("eb", "expected_backend == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "sticky",
        "backend_map_result == expected_backend",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sticky session: same session → same backend");
}

#[test]
fn connection_drain_decreases() {
    let mut ctx = VerificationContext::new();
    for v in &["active_conns", "completed", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ac", "active_conns == 50"));
    ctx.push_obligation(ProofObligation::assume("c", "completed == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == active_conns - completed",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40", "remaining == 40"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drain: 50 - 10 completed = 40 remaining");
}

#[test]
fn max_connections_per_backend() {
    let mut ctx = VerificationContext::new();
    for v in &["current_conns", "max_conns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_add", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cc", "current_conns == 100"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_conns == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "can_add == if current_conns < max_conns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no_add", "can_add == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 conns == max 100 → cannot add");
}

#[test]
fn failover_to_backup() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("primary_healthy", i32_ty());
    ctx.declare_var_typed("use_backup", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ph", "primary_healthy == 0")); // down
    ctx.push_obligation(ProofObligation::assume(
        "ub_def",
        "use_backup == if primary_healthy == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("backup", "use_backup == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "primary down → use backup");
}

#[test]
fn rate_based_selection() {
    // Select backend with lowest request rate
    let mut ctx = VerificationContext::new();
    for v in &["rate_a", "rate_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("select_b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ra", "rate_a == 500"));
    ctx.push_obligation(ProofObligation::assume("rb", "rate_b == 200")); // lower
    ctx.push_obligation(ProofObligation::assume(
        "sb_def",
        "select_b == if rate_b < rate_a { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("b_selected", "select_b == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rate B=200 < A=500 → select B");
}

#[test]
fn total_capacity_across_backends() {
    let mut ctx = VerificationContext::new();
    for v in &["cap_a", "cap_b", "cap_c", "total_cap"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ca", "cap_a == 100"));
    ctx.push_obligation(ProofObligation::assume("cb", "cap_b == 200"));
    ctx.push_obligation(ProofObligation::assume("cc", "cap_c == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "total_cap == cap_a + cap_b + cap_c",
    ));
    ctx.push_obligation(ProofObligation::assert("is_450", "total_cap == 450"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "total capacity: 100+200+150 = 450");
}
