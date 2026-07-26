// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn gain_setting() {
    let mut ctx = VerificationContext::new();
    for v in &["input_level", "gain_db", "output_level"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_headroom", i32_ty());
    // Output = input + gain (in dB). Precompute.
    ctx.push_obligation(ProofObligation::assume("il", "input_level == 60"));
    ctx.push_obligation(ProofObligation::assume("gd", "gain_db == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ol_def",
        "output_level == input_level + gain_db",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "wh_def",
        "within_headroom == if output_level <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "output_level == 80"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_headroom == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Amp: 60 + 20dB gain = 80, ≤ 100 headroom");
}

#[test]
fn speaker_impedance_match() {
    let mut ctx = VerificationContext::new();
    for v in &["speaker_ohms", "min_load_ohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("safe_load", i32_ty());
    ctx.push_obligation(ProofObligation::assume("so", "speaker_ohms == 8"));
    ctx.push_obligation(ProofObligation::assume("mlo", "min_load_ohms == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "sl_def",
        "safe_load == if speaker_ohms >= min_load_ohms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "safe_load == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Amp: 8Ω speaker ≥ 4Ω minimum → safe load");
}

#[test]
fn class_d_pwm_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["pwm_freq_khz", "min_pwm_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("above_audible", i32_ty());
    // Class-D PWM must be well above audible range (>20 kHz)
    ctx.push_obligation(ProofObligation::assume("pf", "pwm_freq_khz == 384"));
    ctx.push_obligation(ProofObligation::assume("mp", "min_pwm_khz == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "above_audible == if pwm_freq_khz >= min_pwm_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "above_audible == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Class-D: 384kHz PWM ≥ 200kHz min → above audible");
}

#[test]
fn thermal_derating() {
    let mut ctx = VerificationContext::new();
    for v in &["ambient_temp_c", "derating_threshold_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_derating", i32_ty());
    ctx.push_obligation(ProofObligation::assume("at", "ambient_temp_c == 70"));
    ctx.push_obligation(ProofObligation::assume("dt", "derating_threshold_c == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "nd_def",
        "needs_derating == if ambient_temp_c > derating_threshold_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_derating == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Amp: 70°C > 60°C threshold → needs derating");
}

#[test]
fn volume_attenuation_steps() {
    let mut ctx = VerificationContext::new();
    for v in &["volume_step", "total_steps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_step", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vs", "volume_step == 45"));
    ctx.push_obligation(ProofObligation::assume("ts", "total_steps == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_step == if volume_step < total_steps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_step == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Amp: volume step 45 < 64 total → valid");
}

#[test]
fn bridge_tied_load_power() {
    let mut ctx = VerificationContext::new();
    for v in &["single_ended_mw", "btl_factor"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("btl_power_mw", u32_ty());
    // BTL delivers 4× single-ended power. Precompute: 500 × 4 = 2000
    ctx.push_obligation(ProofObligation::assume("se", "single_ended_mw == 500"));
    ctx.push_obligation(ProofObligation::assume("bf", "btl_factor == 4"));
    ctx.push_obligation(ProofObligation::assume("bp", "btl_power_mw == 2000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_2000", "btl_power_mw == 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Amp BTL: 500mW × 4 = 2000mW (precomputed)");
}

#[test]
fn mute_control() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mute_active", u32_ty());
    ctx.declare_var_typed("output_enabled", u32_ty());
    ctx.declare_var_typed("audio_output", i32_ty());
    // Output only when not muted AND output enabled
    ctx.push_obligation(ProofObligation::assume("ma", "mute_active == 0"));
    ctx.push_obligation(ProofObligation::assume("oe", "output_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "audio_output == if mute_active == 0 && output_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "audio_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Amp: not muted + output enabled → audio output");
}

#[test]
fn dc_offset_protection() {
    let mut ctx = VerificationContext::new();
    for v in &["dc_offset_mv", "max_dc_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dc_fault", i32_ty());
    ctx.push_obligation(ProofObligation::assume("do", "dc_offset_mv == 150"));
    ctx.push_obligation(ProofObligation::assume("md", "max_dc_mv == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "df_def",
        "dc_fault == if dc_offset_mv > max_dc_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dc_fault == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Amp: DC offset 150mV > 100mV max → fault");
}

#[test]
fn channel_balance() {
    let mut ctx = VerificationContext::new();
    for v in &["left_gain", "right_gain"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("balanced", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lg", "left_gain == 50"));
    ctx.push_obligation(ProofObligation::assume("rg", "right_gain == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "balanced == if left_gain == right_gain { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "balanced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Amp: left=right gain → balanced");
}

#[test]
fn startup_pop_delay() {
    let mut ctx = VerificationContext::new();
    for v in &["startup_ms", "pop_suppress_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pop_free", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sm", "startup_ms == 200"));
    ctx.push_obligation(ProofObligation::assume("psm", "pop_suppress_ms == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "pf_def",
        "pop_free == if startup_ms >= pop_suppress_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pop_free == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Amp: 200ms startup ≥ 150ms suppress → pop-free");
}
