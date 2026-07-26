// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn overflow_period() {
    let mut ctx = VerificationContext::new();
    for v in &["counter_max", "clock_hz", "period_ticks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 16-bit counter: overflows at 65536 ticks
    ctx.push_obligation(ProofObligation::assume("cm", "counter_max == 65535"));
    ctx.push_obligation(ProofObligation::assume("ch", "clock_hz == 1000000")); // 1MHz
    ctx.push_obligation(ProofObligation::assume(
        "pt_def",
        "period_ticks == counter_max + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_65536", "period_ticks == 65536"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "timer: 16-bit overflow at 65536");
}

#[test]
fn prescaler_tick_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["source_hz", "prescaler", "tick_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sh", "source_hz == 72000000")); // 72MHz
    ctx.push_obligation(ProofObligation::assume("ps", "prescaler == 7200"));
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "tick_hz == source_hz / prescaler",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10k", "tick_hz == 10000")); // 10kHz
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "timer: 72MHz/7200=10kHz");
}

#[test]
fn capture_delta() {
    let mut ctx = VerificationContext::new();
    for v in &["capture1", "capture2", "delta"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c1", "capture1 == 15000"));
    ctx.push_obligation(ProofObligation::assume("c2", "capture2 == 25000"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "delta == capture2 - capture1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10000", "delta == 10000"));
    ctx.push_obligation(ProofObligation::assert("positive", "delta > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "timer capture: 25000-15000=10000 ticks");
}

#[test]
fn auto_reload_reset() {
    let mut ctx = VerificationContext::new();
    for v in &["counter", "arr", "new_counter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Auto-reload: counter resets to 0 when it reaches ARR
    ctx.push_obligation(ProofObligation::assume("cnt", "counter == 999"));
    ctx.push_obligation(ProofObligation::assume("a", "arr == 999"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_counter == if counter >= arr { 0 } else { counter + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("resets", "new_counter == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "timer: counter 999 >= ARR 999 → reset to 0");
}

#[test]
fn one_pulse_mode() {
    let mut ctx = VerificationContext::new();
    for v in &["counter", "compare_value", "arr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pulse_active", i32_ty());
    // One-pulse: output high between compare and ARR
    ctx.push_obligation(ProofObligation::assume("cnt", "counter == 500"));
    ctx.push_obligation(ProofObligation::assume("cv", "compare_value == 200"));
    ctx.push_obligation(ProofObligation::assume("a", "arr == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "pa_def",
        "pulse_active == if counter >= compare_value && counter < arr { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("active", "pulse_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "one-pulse: 500 in [200,800) → active");
}

#[test]
fn encoder_mode_position() {
    // Quadrature encoder: count up/down based on direction
    let mut ctx = VerificationContext::new();
    for v in &["old_position", "step_count", "new_position"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("op", "old_position == 1000"));
    ctx.push_obligation(ProofObligation::assume("sc", "step_count == 50")); // forward
    ctx.push_obligation(ProofObligation::assume(
        "np_def",
        "new_position == old_position + step_count",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1050", "new_position == 1050"));
    ctx.push_obligation(ProofObligation::assert(
        "forward",
        "new_position > old_position",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "encoder: position 1000+50=1050");
}

#[test]
fn input_filter_sampling() {
    let mut ctx = VerificationContext::new();
    for v in &["sample_count", "required_stable"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("filtered", i32_ty());
    // Digital filter: input must be stable for N consecutive samples
    ctx.push_obligation(ProofObligation::assume("sc", "sample_count == 8"));
    ctx.push_obligation(ProofObligation::assume("rs", "required_stable == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "filtered == if sample_count >= required_stable { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "filtered == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "timer filter: 8 >= 8 stable → accepted");
}

#[test]
fn slave_mode_trigger() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trigger_source", u32_ty());
    ctx.declare_var_typed("slave_mode", u32_ty());
    ctx.declare_var_typed("counter_enabled", i32_ty());
    // Slave mode: counter enabled by external trigger
    ctx.push_obligation(ProofObligation::assume("ts", "trigger_source == 1")); // active
    ctx.push_obligation(ProofObligation::assume("sm", "slave_mode == 1")); // gated mode
    ctx.push_obligation(ProofObligation::assume(
        "ce_def",
        "counter_enabled == if slave_mode == 1 && trigger_source == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("enabled", "counter_enabled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "timer slave: gated + trigger → enabled");
}

#[test]
fn dma_burst_length() {
    let mut ctx = VerificationContext::new();
    for v in &["burst_transfers", "bytes_per_transfer", "total_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bt", "burst_transfers == 4"));
    ctx.push_obligation(ProofObligation::assume("bpt", "bytes_per_transfer == 2")); // half-word
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bytes == burst_transfers * bytes_per_transfer",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "total_bytes == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "timer DMA: 4×2=8 bytes");
}

#[test]
fn repetition_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["rep_count", "overflows_needed", "update_events"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Update event only after rep_count+1 overflows
    ctx.push_obligation(ProofObligation::assume("rc", "rep_count == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "on_def",
        "overflows_needed == rep_count + 1",
    ));
    ctx.push_obligation(ProofObligation::assume("ue", "update_events == 5")); // after 5*(3+1)=20 overflows
    ctx.push_obligation(ProofObligation::assert("is_4", "overflows_needed == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "timer rep: count=3 → 4 overflows per update");
}
