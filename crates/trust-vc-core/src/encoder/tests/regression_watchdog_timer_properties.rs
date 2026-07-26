// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn timeout_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["counter", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("expired", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "counter == 0"));
    ctx.push_obligation(ProofObligation::assume("t", "threshold == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "expired == if counter <= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "expired == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "watchdog: counter=0 <= threshold=0 → expired");
}

#[test]
fn kick_resets_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["old_counter", "reload_value", "new_counter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_counter == 100")); // partially counted
    ctx.push_obligation(ProofObligation::assume("rv", "reload_value == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_counter == reload_value",
    )); // kick resets
    ctx.push_obligation(ProofObligation::assert("is_10000", "new_counter == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "reset",
        "new_counter > old_counter",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "watchdog kick: 100 → 10000");
}

#[test]
fn countdown_decrement() {
    let mut ctx = VerificationContext::new();
    for v in &["old_counter", "new_counter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oc", "old_counter == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_counter == old_counter - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4999", "new_counter == 4999"));
    ctx.push_obligation(ProofObligation::assert(
        "decreased",
        "new_counter < old_counter",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "watchdog tick: 5000 → 4999");
}

#[test]
fn window_mode_early_kick_invalid() {
    // Window watchdog: kick too early is also a fault
    let mut ctx = VerificationContext::new();
    for v in &["counter", "window_start", "window_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_kick", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "counter == 8000")); // still above window
    ctx.push_obligation(ProofObligation::assume("ws", "window_start == 5000"));
    ctx.push_obligation(ProofObligation::assume("we", "window_end == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "vk_def",
        "valid_kick == if counter <= window_start && counter >= window_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("invalid", "valid_kick == 0")); // too early
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "window WDT: counter 8000 > window 5000 → invalid kick",
    );
}

#[test]
fn window_mode_valid_kick() {
    let mut ctx = VerificationContext::new();
    for v in &["counter", "window_start", "window_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_kick", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "counter == 3000")); // within window
    ctx.push_obligation(ProofObligation::assume("ws", "window_start == 5000"));
    ctx.push_obligation(ProofObligation::assume("we", "window_end == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "vk_def",
        "valid_kick == if counter <= window_start && counter >= window_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "valid_kick == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "window WDT: counter 3000 in [1000,5000] → valid");
}

#[test]
fn prescaler_division() {
    let mut ctx = VerificationContext::new();
    for v in &["clock_hz", "prescaler", "tick_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ch", "clock_hz == 32768")); // typical LPOSC
    ctx.push_obligation(ProofObligation::assume("ps", "prescaler == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "tick_hz == clock_hz / prescaler",
    ));
    ctx.push_obligation(ProofObligation::assert("is_256", "tick_hz == 256"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "WDT prescaler: 32768/128=256 Hz");
}

#[test]
fn timeout_period_ms() {
    let mut ctx = VerificationContext::new();
    for v in &["reload_value", "tick_hz", "timeout_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // timeout_ms = reload_value * 1000 / tick_hz
    // For simplicity, precompute: 256 * 1000 / 256 = 1000ms
    ctx.push_obligation(ProofObligation::assume("rv", "reload_value == 256"));
    ctx.push_obligation(ProofObligation::assume("th", "tick_hz == 256"));
    ctx.push_obligation(ProofObligation::assume("tm", "timeout_ms == 1000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1000", "timeout_ms == 1000"));
    ctx.push_obligation(ProofObligation::assert("reasonable", "timeout_ms > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WDT timeout: 1000ms (256 ticks @ 256Hz)");
}

#[test]
fn reset_action_severity() {
    // 0=interrupt, 1=NMI, 2=system reset
    let mut ctx = VerificationContext::new();
    for v in &["first_timeout_action", "second_timeout_action"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("escalated", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fta", "first_timeout_action == 0")); // interrupt
    ctx.push_obligation(ProofObligation::assume("sta", "second_timeout_action == 2")); // reset
    ctx.push_obligation(ProofObligation::assume(
        "esc_def",
        "escalated == if second_timeout_action > first_timeout_action { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "escalated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WDT escalation: interrupt(0) → reset(2)");
}

#[test]
fn multi_stage_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["stage1_ticks", "stage2_ticks", "total_ticks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s1", "stage1_ticks == 1000"));
    ctx.push_obligation(ProofObligation::assume("s2", "stage2_ticks == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "tt_def",
        "total_ticks == stage1_ticks + stage2_ticks",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1500", "total_ticks == 1500"));
    ctx.push_obligation(ProofObligation::assert(
        "longer",
        "total_ticks > stage1_ticks",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "multi-stage WDT: 1000+500=1500 ticks");
}

#[test]
fn lock_register_protection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("locked", u32_ty());
    ctx.declare_var_typed("write_attempted", u32_ty());
    ctx.declare_var_typed("write_succeeded", i32_ty());
    ctx.push_obligation(ProofObligation::assume("l", "locked == 1")); // register locked
    ctx.push_obligation(ProofObligation::assume("wa", "write_attempted == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "write_succeeded == if locked == 0 && write_attempted == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("blocked", "write_succeeded == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WDT lock: write blocked when locked=1");
}
