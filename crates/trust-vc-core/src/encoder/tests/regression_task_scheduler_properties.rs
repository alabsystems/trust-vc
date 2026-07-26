// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn task_priority_ordering() {
    let mut ctx = VerificationContext::new();
    for v in &["high_prio", "medium_prio", "low_prio"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hp", "high_prio == 1")); // lower number = higher priority
    ctx.push_obligation(ProofObligation::assume("mp", "medium_prio == 5"));
    ctx.push_obligation(ProofObligation::assume("lp", "low_prio == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "order",
        "high_prio < medium_prio && medium_prio < low_prio",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "priority ordering: 1 < 5 < 10");
}

#[test]
fn preemption_on_higher_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["running_prio", "incoming_prio"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_preempt", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rp", "running_prio == 5"));
    ctx.push_obligation(ProofObligation::assume("ip", "incoming_prio == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "sp_def",
        "should_preempt == if incoming_prio < running_prio { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("preempt", "should_preempt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "preempt: incoming 2 < running 5");
}

#[test]
fn deadline_earliest_first() {
    let mut ctx = VerificationContext::new();
    for v in &["deadline_a", "deadline_b", "selected"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("da", "deadline_a == 100"));
    ctx.push_obligation(ProofObligation::assume("db", "deadline_b == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "selected == if deadline_b < deadline_a { deadline_b } else { deadline_a }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_b", "selected == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EDF: select deadline 50 < 100");
}

#[test]
fn time_slice_quantum() {
    let mut ctx = VerificationContext::new();
    for v in &["quantum", "time_used", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("q", "quantum == 10"));
    ctx.push_obligation(ProofObligation::assume("tu", "time_used == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == quantum - time_used",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "remaining == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "quantum: 10 - 7 used = 3 remaining");
}

#[test]
fn total_cpu_utilization() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "task1_time",
        "task2_time",
        "task3_time",
        "total_time",
        "utilization",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t1", "task1_time == 30"));
    ctx.push_obligation(ProofObligation::assume("t2", "task2_time == 20"));
    ctx.push_obligation(ProofObligation::assume("t3", "task3_time == 50"));
    ctx.push_obligation(ProofObligation::assume("tt", "total_time == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "u_def",
        "utilization == (task1_time + task2_time + task3_time) * 100 / total_time",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "utilization == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "utilization: (30+20+50)/100 * 100 = 100%");
}

#[test]
fn waiting_time_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["arrival", "start", "waiting_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "arrival == 5"));
    ctx.push_obligation(ProofObligation::assume("s", "start == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "wt_def",
        "waiting_time == start - arrival",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "waiting_time == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "waiting: start 15 - arrival 5 = 10");
}

#[test]
fn turnaround_time() {
    let mut ctx = VerificationContext::new();
    for v in &["arrival", "completion", "turnaround"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "arrival == 0"));
    ctx.push_obligation(ProofObligation::assume("c", "completion == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "turnaround == completion - arrival",
    ));
    ctx.push_obligation(ProofObligation::assert("is_25", "turnaround == 25"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "turnaround: 25 - 0 = 25");
}

#[test]
fn starvation_prevention_aging() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "base_priority",
        "wait_cycles",
        "age_boost",
        "effective_priority",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bp", "base_priority == 10")); // low priority
    ctx.push_obligation(ProofObligation::assume("wc", "wait_cycles == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ab_def",
        "age_boost == wait_cycles / 10",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "effective_priority == base_priority - age_boost",
    ));
    ctx.push_obligation(ProofObligation::assert("is_0", "effective_priority == 0")); // boosted to top
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "aging: priority 10 - 100/10 boost = 0 (top)");
}

#[test]
fn context_switch_overhead() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "task_time",
        "switch_cost",
        "switches",
        "total_overhead",
        "effective_time",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tt", "task_time == 100"));
    ctx.push_obligation(ProofObligation::assume("sc", "switch_cost == 2"));
    ctx.push_obligation(ProofObligation::assume("sw", "switches == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "total_overhead == switch_cost * switches",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "et_def",
        "effective_time == task_time - total_overhead",
    ));
    ctx.push_obligation(ProofObligation::assert("is_90", "effective_time == 90"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "overhead: 100 - 2*5 = 90 effective");
}

#[test]
fn response_time_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "waiting_time",
        "execution_time",
        "response_time",
        "deadline",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("wt", "waiting_time == 5"));
    ctx.push_obligation(ProofObligation::assume("et", "execution_time == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "rt_def",
        "response_time == waiting_time + execution_time",
    ));
    ctx.push_obligation(ProofObligation::assume("dl", "deadline == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "meets",
        "response_time <= deadline",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response: 5+10 = 15 <= deadline 20");
}
