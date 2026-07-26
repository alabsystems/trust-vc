// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn priority_preemption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_priority", u32_ty());
    ctx.declare_var_typed("incoming_priority", u32_ty());
    ctx.declare_var_typed("should_preempt", i32_ty());
    // Lower number = higher priority (typical RTOS convention)
    ctx.push_obligation(ProofObligation::assume("cp", "current_priority == 5"));
    ctx.push_obligation(ProofObligation::assume("ip", "incoming_priority == 2")); // higher priority
    ctx.push_obligation(ProofObligation::assume(
        "sp_def",
        "should_preempt == if incoming_priority < current_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "should_preempt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS: priority 2 < 5 → preempt");
}

#[test]
fn time_slice_expiry() {
    let mut ctx = VerificationContext::new();
    for v in &["ticks_remaining", "tick_period_us", "elapsed_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("slice_expired", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tr", "ticks_remaining == 0"));
    ctx.push_obligation(ProofObligation::assume("tp", "tick_period_us == 1000")); // 1ms tick
    ctx.push_obligation(ProofObligation::assume("eu", "elapsed_us == 10000")); // 10ms elapsed
    ctx.push_obligation(ProofObligation::assume(
        "se_def",
        "slice_expired == if ticks_remaining == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "slice_expired == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS: 0 ticks remaining → slice expired");
}

#[test]
fn ready_queue_count() {
    let mut ctx = VerificationContext::new();
    for v in &["running", "blocked", "total_tasks", "ready"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Tasks not running or blocked are ready
    ctx.push_obligation(ProofObligation::assume("r", "running == 1"));
    ctx.push_obligation(ProofObligation::assume("b", "blocked == 3"));
    ctx.push_obligation(ProofObligation::assume("tt", "total_tasks == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "rd_def",
        "ready == total_tasks - running - blocked",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "ready == 4"));
    ctx.push_obligation(ProofObligation::assert("positive", "ready > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS: 8 - 1 - 3 = 4 ready tasks");
}

#[test]
fn stack_overflow_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["stack_pointer", "stack_bottom", "guard_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stack_overflow", i32_ty());
    // Stack grows downward; overflow if SP enters guard zone
    ctx.push_obligation(ProofObligation::assume("sp", "stack_pointer == 536870900"));
    ctx.push_obligation(ProofObligation::assume("sb", "stack_bottom == 536870912")); // 0x20000000
    ctx.push_obligation(ProofObligation::assume("gs", "guard_size == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stack_overflow == if stack_pointer < stack_bottom + guard_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stack_overflow == 1")); // 536870900 < 536870944
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS: SP in guard zone → stack overflow");
}

#[test]
fn mutex_priority_inheritance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("owner_priority", u32_ty());
    ctx.declare_var_typed("waiter_priority", u32_ty());
    ctx.declare_var_typed("effective_priority", u32_ty());
    // Priority inheritance: owner runs at highest waiter priority
    ctx.push_obligation(ProofObligation::assume("op", "owner_priority == 10")); // low priority
    ctx.push_obligation(ProofObligation::assume("wp", "waiter_priority == 2")); // high priority
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "effective_priority == if waiter_priority < owner_priority { waiter_priority } else { owner_priority }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "effective_priority == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS mutex: inherit waiter priority 2");
}

#[test]
fn semaphore_count() {
    let mut ctx = VerificationContext::new();
    for v in &["current_count", "max_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("new_count", u32_ty());
    ctx.declare_var_typed("can_take", i32_ty());
    // Counting semaphore: take decrements, give increments
    ctx.push_obligation(ProofObligation::assume("cc", "current_count == 3"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_count == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ct_def",
        "can_take == if current_count > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_count == current_count - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_take == 1"));
    ctx.push_obligation(ProofObligation::assert("is_2", "new_count == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS semaphore: count 3 → take → count 2");
}

#[test]
fn message_queue_space() {
    let mut ctx = VerificationContext::new();
    for v in &["queued_messages", "queue_capacity", "free_slots"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_send", i32_ty());
    ctx.push_obligation(ProofObligation::assume("qm", "queued_messages == 7"));
    ctx.push_obligation(ProofObligation::assume("qc", "queue_capacity == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "fs_def",
        "free_slots == queue_capacity - queued_messages",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "can_send == if free_slots > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_9", "free_slots == 9"));
    ctx.push_obligation(ProofObligation::assert("yes", "can_send == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS queue: 16 - 7 = 9 free slots");
}

#[test]
fn deadline_check() {
    let mut ctx = VerificationContext::new();
    for v in &["current_tick", "deadline_tick"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("missed_deadline", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ct", "current_tick == 1500"));
    ctx.push_obligation(ProofObligation::assume("dt", "deadline_tick == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "md_def",
        "missed_deadline == if current_tick > deadline_tick { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "missed_deadline == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS: tick 1500 > deadline 1000 → missed");
}

#[test]
fn idle_task_runtime() {
    let mut ctx = VerificationContext::new();
    for v in &["total_ticks", "busy_ticks", "idle_ticks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // CPU utilization: idle_ticks = total - busy
    ctx.push_obligation(ProofObligation::assume("tt", "total_ticks == 10000"));
    ctx.push_obligation(ProofObligation::assume("bt", "busy_ticks == 7500"));
    ctx.push_obligation(ProofObligation::assume(
        "it_def",
        "idle_ticks == total_ticks - busy_ticks",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2500", "idle_ticks == 2500"));
    ctx.push_obligation(ProofObligation::assert("has_idle", "idle_ticks > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTOS: 10000 - 7500 = 2500 idle ticks (25%)");
}

#[test]
fn task_notification_value() {
    let mut ctx = VerificationContext::new();
    for v in &["old_notify", "bits_to_set"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("new_notify", u32_ty());
    // Task notification: bitwise OR to set bits
    ctx.push_obligation(ProofObligation::assume("on", "old_notify == 5")); // 0b0101
    ctx.push_obligation(ProofObligation::assume("bs", "bits_to_set == 10")); // 0b1010
    ctx.push_obligation(ProofObligation::assume(
        "nn_def",
        "new_notify == old_notify | bits_to_set",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "new_notify == 15")); // 0b1111
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RTOS notify: 0b0101 | 0b1010 = 0b1111");
}
