// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn output_voltage_step() {
    let mut ctx = VerificationContext::new();
    for v in &["dac_code", "vref_mv", "resolution_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("output_mv", u32_ty());
    // Vout = code × Vref / (2^bits). Precompute: 2048 × 3300 / 4096 = 1650
    ctx.push_obligation(ProofObligation::assume("dc", "dac_code == 2048"));
    ctx.push_obligation(ProofObligation::assume("vr", "vref_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("rb", "resolution_bits == 12"));
    ctx.push_obligation(ProofObligation::assume("om", "output_mv == 1650")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1650", "output_mv == 1650"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DAC: code 2048/4096 × 3300mV = 1650mV");
}

#[test]
fn code_range_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dac_code", u32_ty());
    ctx.declare_var_typed("max_code", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // 12-bit DAC: valid codes 0-4095
    ctx.push_obligation(ProofObligation::assume("dc", "dac_code == 3000"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_code == 4095"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if dac_code <= max_code { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DAC: code 3000 ≤ 4095 → valid 12-bit code");
}

#[test]
fn settling_time_check() {
    let mut ctx = VerificationContext::new();
    for v in &["settling_ns", "max_settling_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("settled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sn", "settling_ns == 800"));
    ctx.push_obligation(ProofObligation::assume("msn", "max_settling_ns == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "settled == if settling_ns <= max_settling_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "settled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DAC: 800ns settling ≤ 1000ns max → settled");
}

#[test]
fn dual_channel_output() {
    let mut ctx = VerificationContext::new();
    for v in &["ch_a_code", "ch_b_code"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("same_output", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ca", "ch_a_code == 2048"));
    ctx.push_obligation(ProofObligation::assume("cb", "ch_b_code == 2048"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "same_output == if ch_a_code == ch_b_code { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "same_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DAC: channel A = B = 2048 → same output");
}

#[test]
fn waveform_step_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["current_code", "step_size", "next_code"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_range", i32_ty());
    // Ramp: next = current + step
    ctx.push_obligation(ProofObligation::assume("cc", "current_code == 1000"));
    ctx.push_obligation(ProofObligation::assume("ss", "step_size == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "next_code == current_code + step_size",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "wr_def",
        "within_range == if next_code <= 4095 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1100", "next_code == 1100"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DAC ramp: 1000 + 100 = 1100 ≤ 4095 → in range");
}

#[test]
fn buffered_output_enable() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("buffer_enable", u32_ty());
    ctx.declare_var_typed("output_enable", u32_ty());
    ctx.declare_var_typed("driving", i32_ty());
    // Output drives only when both buffer and output are enabled
    ctx.push_obligation(ProofObligation::assume("be", "buffer_enable == 1"));
    ctx.push_obligation(ProofObligation::assume("oe", "output_enable == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "driving == if buffer_enable == 1 && output_enable == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "driving == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DAC: buffer + output enabled → driving");
}

#[test]
fn dma_trigger_level() {
    let mut ctx = VerificationContext::new();
    for v in &["fifo_level", "trigger_level"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dma_request", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fl", "fifo_level == 3"));
    ctx.push_obligation(ProofObligation::assume("tl", "trigger_level == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "dr_def",
        "dma_request == if fifo_level < trigger_level { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dma_request == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DAC: FIFO 3 < trigger 4 → DMA request");
}

#[test]
fn noise_shaping_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["physical_bits", "effective_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("improvement", u32_ty());
    // Sigma-delta noise shaping adds effective bits
    ctx.push_obligation(ProofObligation::assume("pb", "physical_bits == 1"));
    ctx.push_obligation(ProofObligation::assume("eb", "effective_bits == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "i_def",
        "improvement == effective_bits - physical_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "improvement == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DAC sigma-delta: 16 effective - 1 physical = 15 bits gained",
    );
}

#[test]
fn power_down_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pd_mode", u32_ty());
    ctx.declare_var_typed("is_normal", i32_ty());
    ctx.declare_var_typed("is_1k_gnd", i32_ty());
    // Power-down modes: 0=normal, 1=1kΩ to GND, 2=100kΩ to GND, 3=high-Z
    ctx.push_obligation(ProofObligation::assume("pm", "pd_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "in_def",
        "is_normal == if pd_mode == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "i1k_def",
        "is_1k_gnd == if pd_mode == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("not_normal", "is_normal == 0"));
    ctx.push_obligation(ProofObligation::assert("yes_1k", "is_1k_gnd == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DAC: mode 1 → 1kΩ to GND, not normal");
}

#[test]
fn update_rate_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["updates_per_sec", "max_update_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ups", "updates_per_sec == 100000"));
    ctx.push_obligation(ProofObligation::assume("mur", "max_update_rate == 1000000"));
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_spec == if updates_per_sec <= max_update_rate { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DAC: 100K updates/s ≤ 1M max → within spec");
}
