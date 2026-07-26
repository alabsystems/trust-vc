// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn priority_preemption() {
    let mut ctx = VerificationContext::new();
    for v in &["running_priority", "ready_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_preempt", i32_ty());
    // Higher numeric priority wins (preempts current)
    ctx.push_obligation(ProofObligation::assume("rp", "running_priority == 5"));
    ctx.push_obligation(ProofObligation::assume("rdp", "ready_priority == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "sp_def",
        "should_preempt == if ready_priority > running_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "should_preempt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS: ready priority 10 > running 5 → preempt");
}

#[test]
fn time_slice_remaining() {
    let mut ctx = VerificationContext::new();
    for v in &["slice_ticks", "elapsed_ticks", "remaining_ticks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("slice_expired", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "slice_ticks == 10"));
    ctx.push_obligation(ProofObligation::assume("et", "elapsed_ticks == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "rt_def",
        "remaining_ticks == slice_ticks - elapsed_ticks",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "se_def",
        "slice_expired == if elapsed_ticks >= slice_ticks { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "remaining_ticks == 3"));
    ctx.push_obligation(ProofObligation::assert("no", "slice_expired == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS: 10 - 7 = 3 ticks remaining, not expired");
}

#[test]
fn semaphore_count() {
    let mut ctx = VerificationContext::new();
    for v in &["sem_count", "max_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_take", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sc", "sem_count == 3"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_count == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ct_def",
        "can_take == if sem_count > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_take == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS semaphore: count 3 > 0 → can take");
}

#[test]
fn deadline_check() {
    let mut ctx = VerificationContext::new();
    for v in &["current_tick", "deadline_tick"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("deadline_missed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ct", "current_tick == 1500"));
    ctx.push_obligation(ProofObligation::assume("dt", "deadline_tick == 1200"));
    ctx.push_obligation(ProofObligation::assume(
        "dm_def",
        "deadline_missed == if current_tick > deadline_tick { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "deadline_missed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS: tick 1500 > deadline 1200 → missed");
}

#[test]
fn task_stack_usage() {
    let mut ctx = VerificationContext::new();
    for v in &["stack_used", "stack_size", "watermark_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stack_warning", i32_ty());
    // Warning if usage exceeds threshold (e.g., 75% = 768 of 1024)
    ctx.push_obligation(ProofObligation::assume("su", "stack_used == 800"));
    ctx.push_obligation(ProofObligation::assume("ss", "stack_size == 1024"));
    ctx.push_obligation(ProofObligation::assume("wt", "watermark_threshold == 768")); // 75%
    ctx.push_obligation(ProofObligation::assume(
        "sw_def",
        "stack_warning == if stack_used > watermark_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stack_warning == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS: stack 800 > 768 (75%) threshold → warning");
}

#[test]
fn message_queue_space() {
    let mut ctx = VerificationContext::new();
    for v in &["queue_count", "queue_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("available", u32_ty());
    ctx.declare_var_typed("can_send", i32_ty());
    ctx.push_obligation(ProofObligation::assume("qc", "queue_count == 7"));
    ctx.push_obligation(ProofObligation::assume("qm", "queue_max == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "available == queue_max - queue_count",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "can_send == if queue_count < queue_max { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_9", "available == 9"));
    ctx.push_obligation(ProofObligation::assert("yes", "can_send == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS queue: 16 - 7 = 9 available, can send");
}

#[test]
fn mutex_priority_ceiling() {
    let mut ctx = VerificationContext::new();
    for v in &["task_priority", "mutex_ceiling"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_lock", i32_ty());
    // Ceiling protocol: task can only lock if priority ≤ ceiling
    ctx.push_obligation(ProofObligation::assume("tp", "task_priority == 5"));
    ctx.push_obligation(ProofObligation::assume("mc", "mutex_ceiling == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "cl_def",
        "can_lock == if task_priority <= mutex_ceiling { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_lock == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "RTOS: task priority 5 ≤ mutex ceiling 10 → can lock",
    );
}

#[test]
fn event_flag_group() {
    let mut ctx = VerificationContext::new();
    for v in &["event_flags", "wait_mask"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("all_set", i32_ty());
    // Wait for all bits in mask to be set. Precompute bitwise AND check.
    // flags=0x0F (15), mask=0x05 (5) → 15 & 5 = 5 = mask → all set
    ctx.push_obligation(ProofObligation::assume("ef", "event_flags == 15"));
    ctx.push_obligation(ProofObligation::assume("wm", "wait_mask == 5"));
    ctx.push_obligation(ProofObligation::assume("as_val", "all_set == 1")); // precomputed
    ctx.push_obligation(ProofObligation::assert("yes", "all_set == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "RTOS events: flags 0x0F & mask 0x05 = 0x05 → all set",
    );
}

#[test]
fn periodic_timer_next_expiry() {
    let mut ctx = VerificationContext::new();
    for v in &["last_expiry_tick", "period_ticks", "next_expiry_tick"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("le", "last_expiry_tick == 5000"));
    ctx.push_obligation(ProofObligation::assume("pt", "period_ticks == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ne_def",
        "next_expiry_tick == last_expiry_tick + period_ticks",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_5100",
        "next_expiry_tick == 5100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS timer: 5000 + 100 period = 5100 next expiry");
}

#[test]
fn task_state_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("task_state", u32_ty());
    ctx.declare_var_typed("is_running", i32_ty());
    ctx.declare_var_typed("is_blocked", i32_ty());
    // States: 0=ready, 1=running, 2=blocked, 3=suspended
    ctx.push_obligation(ProofObligation::assume("ts", "task_state == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_running == if task_state == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "is_blocked == if task_state == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("not_running", "is_running == 0"));
    ctx.push_obligation(ProofObligation::assert("blocked", "is_blocked == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS: state 2 → blocked, not running");
}
