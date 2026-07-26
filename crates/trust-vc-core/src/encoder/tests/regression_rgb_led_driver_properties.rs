// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn color_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["bits_per_channel", "min_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("depth_ok", i32_ty());
    // 8-bit per channel = 256 levels per R/G/B
    ctx.push_obligation(ProofObligation::assume("bc", "bits_per_channel == 8"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bits == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "depth_ok == if bits_per_channel >= min_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "depth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RGB LED: 8 bits/channel ≥ 8 min → depth OK");
}

#[test]
fn pwm_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["pwm_freq_hz", "min_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flicker_free", i32_ty());
    // PWM frequency >200Hz avoids visible flicker
    ctx.push_obligation(ProofObligation::assume("pf", "pwm_freq_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume("mf", "min_freq_hz == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ff_def",
        "flicker_free == if pwm_freq_hz >= min_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flicker_free == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RGB LED: 1000 Hz PWM ≥ 200 Hz → flicker free");
}

#[test]
fn forward_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "max_current_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("current_ok", i32_ty());
    // Max forward current per LED (typically 20mA per channel)
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma == 15"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_ma == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "current_ok == if current_ma <= max_current_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RGB LED: 15mA ≤ 20mA max → current OK");
}

#[test]
fn resistor_value() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "forward_mv", "target_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resistor_ohms", u32_ty());
    // R = (Vsupply - Vf) / I. Precompute: (5000 - 2000) / 20 = 150Ω
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("fm", "forward_mv == 2000"));
    ctx.push_obligation(ProofObligation::assume("tm", "target_ma == 20"));
    ctx.push_obligation(ProofObligation::assume("ro", "resistor_ohms == 150")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_150", "resistor_ohms == 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "RGB LED: (5V-2V)/20mA = 150Ω resistor (precomputed)",
    );
}

#[test]
fn white_balance() {
    let mut ctx = VerificationContext::new();
    for v in &["r_value", "g_value", "b_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_white", i32_ty());
    // Approximate white: R≈G≈B (all equal)
    ctx.push_obligation(ProofObligation::assume("rv", "r_value == 255"));
    ctx.push_obligation(ProofObligation::assume("gv", "g_value == 255"));
    ctx.push_obligation(ProofObligation::assume("bv", "b_value == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "iw_def",
        "is_white == if r_value == g_value && g_value == b_value { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_white == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RGB LED: R=G=B=255 → white");
}

#[test]
fn led_count_chain() {
    let mut ctx = VerificationContext::new();
    for v in &["num_leds", "max_chain"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("chain_ok", i32_ty());
    // WS2812 chain: limited by timing and voltage drop
    ctx.push_obligation(ProofObligation::assume("nl", "num_leds == 60"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_chain == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "chain_ok == if num_leds <= max_chain { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "chain_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RGB LED: 60 LEDs ≤ 300 max chain → chain OK");
}

#[test]
fn power_budget() {
    let mut ctx = VerificationContext::new();
    for v in &["num_leds", "power_per_led_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("total_power_mw", u32_ty());
    ctx.declare_var_typed("within_budget", i32_ty());
    // Total power = count × per-LED. Precompute: 60 × 60 = 3600mW
    ctx.push_obligation(ProofObligation::assume("nl", "num_leds == 60"));
    ctx.push_obligation(ProofObligation::assume("pp", "power_per_led_mw == 60"));
    ctx.push_obligation(ProofObligation::assume("tp", "total_power_mw == 3600")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "within_budget == if total_power_mw <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3600", "total_power_mw == 3600"));
    ctx.push_obligation(ProofObligation::assert("yes", "within_budget == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "RGB LED: 60 × 60mW = 3600mW ≤ 5W budget (precomputed)",
    );
}

#[test]
fn gamma_correction() {
    let mut ctx = VerificationContext::new();
    for v in &["input_value", "gamma_output"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gamma 2.2 lookup: input 128 → output ~55 (precomputed)
    ctx.push_obligation(ProofObligation::assume("iv", "input_value == 128"));
    ctx.push_obligation(ProofObligation::assume("go", "gamma_output == 55")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_55", "gamma_output == 55"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "RGB LED: gamma(128) = 55 (precomputed γ=2.2 lookup)",
    );
}

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["bit_rate_khz", "min_rate_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // WS2812: 800kHz data rate
    ctx.push_obligation(ProofObligation::assume("br", "bit_rate_khz == 800"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_rate_khz == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if bit_rate_khz >= min_rate_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RGB LED: 800 kHz ≥ 400 kHz min → data rate OK");
}

#[test]
fn brightness_level() {
    let mut ctx = VerificationContext::new();
    for v in &["brightness", "max_brightness"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("level_ok", i32_ty());
    // Global brightness: 0-31 (5-bit) on APA102, 0-255 on WS2812
    ctx.push_obligation(ProofObligation::assume("b", "brightness == 20"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_brightness == 31"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "level_ok == if brightness <= max_brightness { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "level_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RGB LED: brightness 20 ≤ 31 max → level OK");
}
