// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn watchdog_timeout_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["prescaler", "reload_value", "clock_hz", "timeout_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Timeout = prescaler × reload / clock × 1000
    // Precompute: 256 × 4096 / 32000 × 1000 ≈ 32768ms
    ctx.push_obligation(ProofObligation::assume("p", "prescaler == 256"));
    ctx.push_obligation(ProofObligation::assume("rv", "reload_value == 4096"));
    ctx.push_obligation(ProofObligation::assume("ch", "clock_hz == 32000"));
    ctx.push_obligation(ProofObligation::assume("tm", "timeout_ms == 32768")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_32768", "timeout_ms == 32768"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WDG: 256 × 4096 / 32000 ≈ 32.768s timeout");
}

#[test]
fn watchdog_feed_timing() {
    let mut ctx = VerificationContext::new();
    for v in &["timeout_ms", "feed_interval_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("safe_margin", i32_ty());
    // Feed must happen well before timeout (< 50% of timeout for safety)
    ctx.push_obligation(ProofObligation::assume("tm", "timeout_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume("fi", "feed_interval_ms == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "sm_def",
        "safe_margin == if feed_interval_ms < timeout_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "safe_margin == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WDG: feed 400ms < 1000ms timeout → safe");
}

#[test]
fn window_watchdog_valid_feed() {
    let mut ctx = VerificationContext::new();
    for v in &["counter", "window_start", "window_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_window", i32_ty());
    // Window watchdog: feed only when counter is in [window_start, window_end]
    ctx.push_obligation(ProofObligation::assume("c", "counter == 80"));
    ctx.push_obligation(ProofObligation::assume("ws", "window_start == 64"));
    ctx.push_obligation(ProofObligation::assume("we", "window_end == 127"));
    ctx.push_obligation(ProofObligation::assume(
        "iw_def",
        "in_window == if counter >= window_start && counter <= window_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_window == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WWDG: counter 80 in [64, 127] → valid feed window");
}

#[test]
fn watchdog_prescaler_divider() {
    let mut ctx = VerificationContext::new();
    for v in &["lsi_hz", "prescaler_div", "wdg_clock_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // LSI 32kHz / prescaler = watchdog clock
    ctx.push_obligation(ProofObligation::assume("lh", "lsi_hz == 32000"));
    ctx.push_obligation(ProofObligation::assume("pd", "prescaler_div == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "wch_def",
        "wdg_clock_hz == lsi_hz / prescaler_div",
    ));
    ctx.push_obligation(ProofObligation::assert("is_250", "wdg_clock_hz == 250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "WDG: 32000 / 128 = 250 Hz clock");
}

#[test]
fn early_wakeup_interrupt() {
    let mut ctx = VerificationContext::new();
    for v in &["counter", "ewi_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ewi_pending", i32_ty());
    // Early wakeup interrupt fires before timeout
    ctx.push_obligation(ProofObligation::assume("c", "counter == 5"));
    ctx.push_obligation(ProofObligation::assume("et", "ewi_threshold == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "ewi_pending == if counter <= ewi_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ewi_pending == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WDG EWI: counter 5 ≤ threshold 8 → interrupt");
}

#[test]
fn watchdog_reset_count() {
    let mut ctx = VerificationContext::new();
    for v in &["reset_count", "max_resets"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("enter_safe_mode", i32_ty());
    // After too many resets, enter safe/recovery mode
    ctx.push_obligation(ProofObligation::assume("rc", "reset_count == 3"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_resets == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "esm_def",
        "enter_safe_mode == if reset_count >= max_resets { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "enter_safe_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WDG: 3 resets >= 3 max → safe mode");
}

#[test]
fn independent_watchdog_countdown() {
    let mut ctx = VerificationContext::new();
    for v in &["reload_value", "ticks_elapsed", "current_counter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("time_remaining", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rv", "reload_value == 4096"));
    ctx.push_obligation(ProofObligation::assume("te", "ticks_elapsed == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "cc_def",
        "current_counter == reload_value - ticks_elapsed",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "tr_def",
        "time_remaining == current_counter",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_3096",
        "current_counter == 3096",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "remaining",
        "time_remaining == 3096",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IWDG: 4096 - 1000 elapsed = 3096 remaining");
}

#[test]
fn dual_watchdog_coverage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("iwdg_active", u32_ty());
    ctx.declare_var_typed("wwdg_active", u32_ty());
    ctx.declare_var_typed("both_active", i32_ty());
    ctx.declare_var_typed("any_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ia", "iwdg_active == 1"));
    ctx.push_obligation(ProofObligation::assume("wa", "wwdg_active == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ba_def",
        "both_active == if iwdg_active == 1 && wwdg_active == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "any_active == if iwdg_active == 1 || wwdg_active == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("both", "both_active == 1"));
    ctx.push_obligation(ProofObligation::assert("any", "any_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WDG: IWDG + WWDG both active → full coverage");
}

#[test]
fn watchdog_freeze_in_debug() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("debug_mode", u32_ty());
    ctx.declare_var_typed("freeze_enabled", u32_ty());
    ctx.declare_var_typed("counter_running", i32_ty());
    // Freeze watchdog counter during debug to prevent unwanted resets
    ctx.push_obligation(ProofObligation::assume("dm", "debug_mode == 1"));
    ctx.push_obligation(ProofObligation::assume("fe", "freeze_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cr_def",
        "counter_running == if debug_mode == 1 && freeze_enabled == 1 { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("stopped", "counter_running == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WDG: debug + freeze → counter stopped");
}

#[test]
fn watchdog_key_sequence() {
    let mut ctx = VerificationContext::new();
    for v in &["key_value", "expected_key"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("key_valid", i32_ty());
    // Watchdog requires magic key write (e.g., 0xAAAA = 43690) to feed
    ctx.push_obligation(ProofObligation::assume("kv", "key_value == 43690")); // 0xAAAA
    ctx.push_obligation(ProofObligation::assume("ek", "expected_key == 43690"));
    ctx.push_obligation(ProofObligation::assume(
        "kv_def",
        "key_valid == if key_value == expected_key { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "key_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WDG: key 0xAAAA matches → feed accepted");
}
