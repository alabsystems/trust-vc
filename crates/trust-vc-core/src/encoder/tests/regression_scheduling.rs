// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn highest_priority_first() {
    let mut ctx = VerificationContext::new();
    for v in &["p_a", "p_b", "p_c", "selected"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Lower number = higher priority
    ctx.push_obligation(ProofObligation::assume("pa", "p_a == 3"));
    ctx.push_obligation(ProofObligation::assume("pb", "p_b == 1"));
    ctx.push_obligation(ProofObligation::assume("pc", "p_c == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "sel_def",
        "selected == if p_a <= p_b && p_a <= p_c { 0 } else { if p_b <= p_c { 1 } else { 2 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("pick_b", "selected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "priority scheduling: pick task B (priority 1)");
}

#[test]
fn round_robin_advance() {
    let mut ctx = VerificationContext::new();
    for v in &["current", "num_tasks", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cur", "current == 2"));
    ctx.push_obligation(ProofObligation::assume("nt", "num_tasks == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == if current + 1 == num_tasks { 0 } else { current + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "next == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "round robin: 2 → 3 (of 4 tasks)");
}

#[test]
fn round_robin_wraps() {
    let mut ctx = VerificationContext::new();
    for v in &["current", "num_tasks", "next"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cur", "current == 3"));
    ctx.push_obligation(ProofObligation::assume("nt", "num_tasks == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next == if current + 1 == num_tasks { 0 } else { current + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "next == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "round robin: 3 → 0 (wraps)");
}

#[test]
fn earliest_deadline_first() {
    let mut ctx = VerificationContext::new();
    for v in &["d_a", "d_b", "d_c", "selected"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("da", "d_a == 50"));
    ctx.push_obligation(ProofObligation::assume("db", "d_b == 30"));
    ctx.push_obligation(ProofObligation::assume("dc", "d_c == 70"));
    ctx.push_obligation(ProofObligation::assume(
        "sel_def",
        "selected == if d_a <= d_b && d_a <= d_c { 0 } else { if d_b <= d_c { 1 } else { 2 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("pick_b", "selected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EDF: pick task B (deadline 30)");
}

#[test]
fn time_slice_remaining() {
    let mut ctx = VerificationContext::new();
    for v in &["quantum", "used", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("q", "quantum == 10"));
    ctx.push_obligation(ProofObligation::assume("u", "used == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "rem_def",
        "remaining == quantum - used",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "remaining == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "time slice: 10 - 7 = 3 remaining");
}

#[test]
fn preemption_on_higher_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["running_priority", "arriving_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("preempt", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rp", "running_priority == 5"));
    ctx.push_obligation(ProofObligation::assume("ap", "arriving_priority == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "preempt_def",
        "preempt == if arriving_priority < running_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("should_preempt", "preempt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "preempt: arriving priority 2 < running 5");
}

#[test]
fn turnaround_time() {
    let mut ctx = VerificationContext::new();
    for v in &["arrival", "completion", "turnaround"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("arr", "arrival == 5"));
    ctx.push_obligation(ProofObligation::assume("comp", "completion == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "turn_def",
        "turnaround == completion - arrival",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "turnaround == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "turnaround: 15 - 5 = 10");
}

#[test]
fn waiting_time() {
    let mut ctx = VerificationContext::new();
    for v in &["arrival", "start", "waiting"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("arr", "arrival == 5"));
    ctx.push_obligation(ProofObligation::assume("st", "start == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "wait_def",
        "waiting == start - arrival",
    ));
    ctx.push_obligation(ProofObligation::assert("is_7", "waiting == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "waiting time: 12 - 5 = 7");
}

#[test]
fn sjf_shortest_first() {
    // Shortest Job First: pick task with smallest burst time
    let mut ctx = VerificationContext::new();
    for v in &["burst_a", "burst_b", "burst_c", "selected"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ba", "burst_a == 8"));
    ctx.push_obligation(ProofObligation::assume("bb", "burst_b == 3"));
    ctx.push_obligation(ProofObligation::assume("bc", "burst_c == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "sel_def",
        "selected == if burst_a <= burst_b && burst_a <= burst_c { 0 } else { if burst_b <= burst_c { 1 } else { 2 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("pick_b", "selected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SJF: pick task B (burst 3)");
}

#[test]
fn utilization_two_tasks() {
    // CPU utilization = sum of burst times / total time
    let mut ctx = VerificationContext::new();
    for v in &["burst_a", "burst_b", "idle", "total_time", "busy_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ba", "burst_a == 4"));
    ctx.push_obligation(ProofObligation::assume("bb", "burst_b == 3"));
    ctx.push_obligation(ProofObligation::assume("idle_val", "idle == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "busy_def",
        "busy_time == burst_a + burst_b",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "total_def",
        "total_time == busy_time + idle",
    ));
    ctx.push_obligation(ProofObligation::assert("busy_7", "busy_time == 7"));
    ctx.push_obligation(ProofObligation::assert("total_10", "total_time == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "utilization: 4+3 busy, 3 idle = 10 total");
}
