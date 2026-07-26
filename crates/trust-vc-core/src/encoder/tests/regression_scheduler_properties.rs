// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn round_robin_quantum_expires() {
    let mut ctx = VerificationContext::new();
    for v in &["time_used", "quantum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("preempt", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tu", "time_used == 10"));
    ctx.push_obligation(ProofObligation::assume("q", "quantum == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "preempt == if time_used >= quantum { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("preempted", "preempt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "time 10 >= quantum 10 → preempt");
}

#[test]
fn priority_higher_runs_first() {
    let mut ctx = VerificationContext::new();
    for v in &["priority_a", "priority_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("a_runs_first", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pa", "priority_a == 10")); // higher = more urgent
    ctx.push_obligation(ProofObligation::assume("pb", "priority_b == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "arf_def",
        "a_runs_first == if priority_a > priority_b { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("first", "a_runs_first == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "priority 10 > 5 → task A runs first");
}

#[test]
fn sjf_shortest_job_first() {
    let mut ctx = VerificationContext::new();
    for v in &["burst_a", "burst_b", "burst_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("shortest", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ba", "burst_a == 8"));
    ctx.push_obligation(ProofObligation::assume("bb", "burst_b == 3"));
    ctx.push_obligation(ProofObligation::assume("bc", "burst_c == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "shortest == if burst_b <= burst_a && burst_b <= burst_c { burst_b } else { if burst_a <= burst_c { burst_a } else { burst_c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "shortest == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SJF: min(8,3,5) = 3");
}

#[test]
fn deadline_remaining_time() {
    let mut ctx = VerificationContext::new();
    for v in &["deadline", "current_time", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d", "deadline == 1000"));
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 700"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remaining == deadline - current_time",
    ));
    ctx.push_obligation(ProofObligation::assert("is_300", "remaining == 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "deadline 1000 - time 700 = 300 remaining");
}

#[test]
fn multilevel_queue_promotion() {
    // Starved task gets promoted to higher queue
    let mut ctx = VerificationContext::new();
    for v in &[
        "wait_time",
        "starvation_threshold",
        "current_queue",
        "new_queue",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("wt", "wait_time == 100"));
    ctx.push_obligation(ProofObligation::assume("st", "starvation_threshold == 50"));
    ctx.push_obligation(ProofObligation::assume("cq", "current_queue == 2")); // lower priority
    ctx.push_obligation(ProofObligation::assume(
        "nq_def",
        "new_queue == if wait_time > starvation_threshold { current_queue - 1 } else { current_queue }",
    ));
    ctx.push_obligation(ProofObligation::assert("promoted", "new_queue == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wait 100 > threshold 50 → promote queue 2→1");
}

#[test]
fn cpu_utilization_percentage() {
    let mut ctx = VerificationContext::new();
    for v in &["busy_time", "total_time", "utilization"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bt", "busy_time == 80"));
    ctx.push_obligation(ProofObligation::assume("tt", "total_time == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "u_def",
        "utilization == busy_time * 100 / total_time",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "utilization == 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "utilization: 80/100 = 80%");
}

#[test]
fn context_switch_overhead() {
    let mut ctx = VerificationContext::new();
    for v in &["switches", "cost_per_switch", "total_overhead"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sw", "switches == 100"));
    ctx.push_obligation(ProofObligation::assume("cps", "cost_per_switch == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "total_overhead == switches * cost_per_switch",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "total_overhead == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "100 switches * 5 cost = 500 overhead");
}

#[test]
fn fair_share_allocation() {
    // Each of N tasks gets 1/N of CPU
    let mut ctx = VerificationContext::new();
    for v in &["total_cpu", "num_tasks", "per_task"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tc", "total_cpu == 100"));
    ctx.push_obligation(ProofObligation::assume("nt", "num_tasks == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "pt_def",
        "per_task == total_cpu / num_tasks",
    ));
    ctx.push_obligation(ProofObligation::assert("is_25", "per_task == 25"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "fair share: 100 / 4 = 25 per task");
}

#[test]
fn ready_queue_non_empty_means_runnable() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ready_count", u32_ty());
    ctx.declare_var_typed("has_runnable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "ready_count == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "hr_def",
        "has_runnable == if ready_count > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("runnable", "has_runnable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 ready tasks → has runnable");
}

#[test]
fn turnaround_time() {
    // Turnaround = completion - arrival
    let mut ctx = VerificationContext::new();
    for v in &["arrival", "completion", "turnaround"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "arrival == 10"));
    ctx.push_obligation(ProofObligation::assume("c", "completion == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "turnaround == completion - arrival",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "turnaround == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "turnaround: 25 - 10 = 15");
}
