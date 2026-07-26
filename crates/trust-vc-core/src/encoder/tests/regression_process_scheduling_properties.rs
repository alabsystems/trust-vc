// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn process_state_transition_ready_to_running() {
    // States: 0=New, 1=Ready, 2=Running, 3=Waiting, 4=Terminated
    let mut ctx = VerificationContext::new();
    for v in &["state_before", "state_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sb", "state_before == 1")); // Ready
    ctx.push_obligation(ProofObligation::assume("sa", "state_after == 2")); // Running
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "state_after > state_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "state: Ready(1) → Running(2)");
}

#[test]
fn nice_value_affects_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["base_priority", "nice_value", "effective_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bp", "base_priority == 20"));
    ctx.push_obligation(ProofObligation::assume("nv", "nice_value == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "effective_priority == base_priority + nice_value",
    ));
    ctx.push_obligation(ProofObligation::assert("is_25", "effective_priority == 25"));
    ctx.push_obligation(ProofObligation::assert(
        "lower",
        "effective_priority > base_priority",
    )); // higher nice = lower priority
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nice +5: priority 20 → 25 (lower)");
}

#[test]
fn cpu_shares_proportional() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "process_a_shares",
        "process_b_shares",
        "total_shares",
        "a_pct",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pas", "process_a_shares == 75"));
    ctx.push_obligation(ProofObligation::assume("pbs", "process_b_shares == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "ts_def",
        "total_shares == process_a_shares + process_b_shares",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ap_def",
        "a_pct == process_a_shares * 100 / total_shares",
    ));
    ctx.push_obligation(ProofObligation::assert("is_75", "a_pct == 75"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "CPU shares: 75/(75+25) * 100 = 75%");
}

#[test]
fn fork_creates_child() {
    let mut ctx = VerificationContext::new();
    for v in &["processes_before", "processes_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pb", "processes_before == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "pa_def",
        "processes_after == processes_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_11", "processes_after == 11"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fork: 10 → 11 processes");
}

#[test]
fn exit_removes_process() {
    let mut ctx = VerificationContext::new();
    for v in &["processes_before", "processes_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pb", "processes_before == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "pa_def",
        "processes_after == processes_before - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_9", "processes_after == 9"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "exit: 10 → 9 processes");
}

#[test]
fn cgroup_cpu_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["cpu_usage", "cpu_limit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("throttled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cu", "cpu_usage == 90"));
    ctx.push_obligation(ProofObligation::assume("cl", "cpu_limit == 80")); // percentage
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "throttled == if cpu_usage > cpu_limit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_throttled", "throttled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cgroup: 90% usage > 80% limit → throttled");
}

#[test]
fn pid_uniqueness() {
    let mut ctx = VerificationContext::new();
    for v in &["pid_a", "pid_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pa", "pid_a == 1234"));
    ctx.push_obligation(ProofObligation::assume("pb", "pid_b == 5678"));
    ctx.push_obligation(ProofObligation::assert("unique", "pid_a != pid_b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PIDs unique: 1234 != 5678");
}

#[test]
fn virtual_runtime_fairness() {
    let mut ctx = VerificationContext::new();
    for v in &["vruntime_a", "vruntime_b", "max_diff", "actual_diff"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fair", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vra", "vruntime_a == 1000"));
    ctx.push_obligation(ProofObligation::assume("vrb", "vruntime_b == 1005"));
    ctx.push_obligation(ProofObligation::assume("md", "max_diff == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ad_def",
        "actual_diff == vruntime_b - vruntime_a",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fair == if actual_diff <= max_diff { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_fair", "fair == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CFS: |1000-1005|=5 <= 10 → fair");
}

#[test]
fn zombie_process_cleanup() {
    let mut ctx = VerificationContext::new();
    for v in &["zombies_before", "waited", "zombies_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("zb", "zombies_before == 5"));
    ctx.push_obligation(ProofObligation::assume("w", "waited == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "za_def",
        "zombies_after == zombies_before - waited",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "zombies_after == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zombie cleanup: 5 - 3 waited = 2 remaining");
}

#[test]
fn affinity_mask_cpu_selection() {
    let mut ctx = VerificationContext::new();
    for v in &["total_cpus", "allowed_cpus", "selected_cpu"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tc", "total_cpus == 8"));
    ctx.push_obligation(ProofObligation::assume("ac", "allowed_cpus == 4")); // half pinned
    ctx.push_obligation(ProofObligation::assume("sc", "selected_cpu == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "within_allowed",
        "selected_cpu < allowed_cpus",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "within_total",
        "selected_cpu < total_cpus",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "affinity: CPU 2 within 4 allowed of 8 total");
}
