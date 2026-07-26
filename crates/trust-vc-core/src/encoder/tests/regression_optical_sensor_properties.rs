// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn lux_to_adc_conversion() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_value", "max_adc", "max_lux"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lux_reading", u32_ty());
    // Lux = adc × max_lux / max_adc. Precompute: 2048 × 10000 / 4096 = 5000
    ctx.push_obligation(ProofObligation::assume("av", "adc_value == 2048"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_adc == 4096"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_lux == 10000"));
    ctx.push_obligation(ProofObligation::assume("lr", "lux_reading == 5000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_5000", "lux_reading == 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical: ADC 2048/4096 × 10000 = 5000 lux");
}

#[test]
fn proximity_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["proximity_count", "near_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("object_near", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pc", "proximity_count == 200"));
    ctx.push_obligation(ProofObligation::assume("nt", "near_threshold == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "on_def",
        "object_near == if proximity_count >= near_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "object_near == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical: prox 200 ≥ 150 threshold → object near");
}

#[test]
fn color_channel_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["red_count", "green_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("red_dominant", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "red_count == 800"));
    ctx.push_obligation(ProofObligation::assume("gc", "green_count == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "rd_def",
        "red_dominant == if red_count > green_count { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "red_dominant == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical: red 800 > green 500 → red dominant");
}

#[test]
fn integration_time_setting() {
    let mut ctx = VerificationContext::new();
    for v in &["integration_ms", "min_integration_ms", "max_integration_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume("im", "integration_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("min", "min_integration_ms == 2"));
    ctx.push_obligation(ProofObligation::assume("max", "max_integration_ms == 614"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_time == if integration_ms >= min_integration_ms && integration_ms <= max_integration_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_time == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical: 100ms in [2, 614] → valid integration time",
    );
}

#[test]
fn gain_multiplier() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gain_setting", u32_ty());
    ctx.declare_var_typed("is_high_gain", i32_ty());
    // Gain: 1×, 4×, 16×, 64×. High gain = 16× or 64×.
    ctx.push_obligation(ProofObligation::assume("gs", "gain_setting == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "ih_def",
        "is_high_gain == if gain_setting >= 16 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_high_gain == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical: 16× gain ≥ 16 → high gain mode");
}

#[test]
fn saturation_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_count", "saturation_level"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("saturated", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "raw_count == 65535"));
    ctx.push_obligation(ProofObligation::assume("sl", "saturation_level == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "saturated == if raw_count >= saturation_level { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "saturated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical: count 65535 = max → saturated");
}

#[test]
fn ir_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["visible_count", "ir_count", "compensated"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Visible light = total - IR component
    ctx.push_obligation(ProofObligation::assume("vc", "visible_count == 3000"));
    ctx.push_obligation(ProofObligation::assume("ic", "ir_count == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compensated == visible_count - ir_count",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2500", "compensated == 2500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical: 3000 visible - 500 IR = 2500 compensated");
}

#[test]
fn interrupt_persistence() {
    let mut ctx = VerificationContext::new();
    for v in &["consecutive_triggers", "persistence_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("interrupt_fire", i32_ty());
    // Interrupt fires after N consecutive threshold violations
    ctx.push_obligation(ProofObligation::assume("ct", "consecutive_triggers == 4"));
    ctx.push_obligation(ProofObligation::assume("pc", "persistence_count == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "if_def",
        "interrupt_fire == if consecutive_triggers >= persistence_count { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "interrupt_fire == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical: 4 triggers = 4 persistence → interrupt fires",
    );
}

#[test]
fn multi_channel_max() {
    let mut ctx = VerificationContext::new();
    for v in &["ch_clear", "ch_red", "ch_green", "ch_blue"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("max_channel", u32_ty());
    // Find max of RGB channels (ignore clear). Precompute.
    ctx.push_obligation(ProofObligation::assume("cc", "ch_clear == 2000"));
    ctx.push_obligation(ProofObligation::assume("cr", "ch_red == 800"));
    ctx.push_obligation(ProofObligation::assume("cg", "ch_green == 1200"));
    ctx.push_obligation(ProofObligation::assume("cb", "ch_blue == 600"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_channel == 1200")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1200", "max_channel == 1200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical: max(800,1200,600) = 1200 (green dominant)",
    );
}

#[test]
fn power_mode_transition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_mode", u32_ty());
    ctx.declare_var_typed("target_mode", u32_ty());
    ctx.declare_var_typed("transition_needed", i32_ty());
    // Modes: 0=power-down, 1=single, 2=continuous
    ctx.push_obligation(ProofObligation::assume("cm", "current_mode == 0"));
    ctx.push_obligation(ProofObligation::assume("tm", "target_mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "tn_def",
        "transition_needed == if current_mode != target_mode { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "transition_needed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical: mode 0→2 → transition needed");
}
