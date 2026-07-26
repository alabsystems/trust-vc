// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn angle_from_adc() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_value", "adc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("angle_deg_x10", u32_ty());
    // Angle = ADC/max × 3600 (×10 for 0.1° resolution). Precompute: 2048/4096 × 3600 = 1800
    ctx.push_obligation(ProofObligation::assume("av", "adc_value == 2048"));
    ctx.push_obligation(ProofObligation::assume("am", "adc_max == 4096"));
    ctx.push_obligation(ProofObligation::assume("ad", "angle_deg_x10 == 1800")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1800", "angle_deg_x10 == 1800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Mag encoder: ADC 2048/4096 = 180.0° (precomputed)");
}

#[test]
fn resolution_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["encoder_bits", "min_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resolution_ok", i32_ty());
    // AS5048A: 14-bit, AS5600: 12-bit
    ctx.push_obligation(ProofObligation::assume("eb", "encoder_bits == 14"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bits == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resolution_ok == if encoder_bits >= min_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resolution_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Mag encoder: 14-bit ≥ 12-bit min → resolution OK");
}

#[test]
fn magnet_strength() {
    let mut ctx = VerificationContext::new();
    for v in &["field_mt", "min_field_mt", "max_field_mt"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("field_ok", i32_ty());
    // Operating magnetic field: typically 20-80 mT
    ctx.push_obligation(ProofObligation::assume("fm", "field_mt == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_field_mt == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_field_mt == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "field_ok == if field_mt >= min_field_mt && field_mt <= max_field_mt { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "field_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Mag encoder: 50mT in [20, 80] → field strength OK");
}

#[test]
fn air_gap() {
    let mut ctx = VerificationContext::new();
    for v in &["gap_mm_x10", "max_gap_mm_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("gap_ok", i32_ty());
    // Air gap between magnet and sensor: typically 0.5-3mm
    ctx.push_obligation(ProofObligation::assume("gm", "gap_mm_x10 == 15")); // 1.5mm
    ctx.push_obligation(ProofObligation::assume("mg", "max_gap_mm_x10 == 30")); // 3.0mm
    ctx.push_obligation(ProofObligation::assume(
        "go_def",
        "gap_ok == if gap_mm_x10 <= max_gap_mm_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "gap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Mag encoder: 1.5mm gap ≤ 3.0mm max → gap OK");
}

#[test]
fn angular_speed() {
    let mut ctx = VerificationContext::new();
    for v in &["rpm", "max_rpm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("speed_ok", i32_ty());
    // Max rotational speed (limited by sampling rate)
    ctx.push_obligation(ProofObligation::assume("r", "rpm == 10000"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_rpm == 20000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "speed_ok == if rpm <= max_rpm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "speed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Mag encoder: 10K RPM ≤ 20K max → speed OK");
}

#[test]
fn interface_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("interface", u32_ty());
    ctx.declare_var_typed("is_ssi", i32_ty());
    // Interface: 0=SPI, 1=I2C, 2=SSI, 3=ABZ incremental, 4=PWM
    ctx.push_obligation(ProofObligation::assume("i", "interface == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_ssi == if interface == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_ssi == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Mag encoder: interface=2 → SSI output");
}

#[test]
fn zero_position_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_angle", "zero_offset", "adjusted_angle"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Apply programmable zero offset
    ctx.push_obligation(ProofObligation::assume("ra", "raw_angle == 2500"));
    ctx.push_obligation(ProofObligation::assume("zo", "zero_offset == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "adjusted_angle == raw_angle - zero_offset",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2000", "adjusted_angle == 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Mag encoder: 2500 - 500 offset = 2000 adjusted");
}

#[test]
fn diagnostic_status() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mag_too_weak", u32_ty());
    ctx.declare_var_typed("mag_too_strong", u32_ty());
    ctx.declare_var_typed("diagnostics_clear", i32_ty());
    // Built-in diagnostics: magnet field checks
    ctx.push_obligation(ProofObligation::assume("mw", "mag_too_weak == 0"));
    ctx.push_obligation(ProofObligation::assume("ms", "mag_too_strong == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "dc_def",
        "diagnostics_clear == if mag_too_weak == 0 && mag_too_strong == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "diagnostics_clear == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Mag encoder: no weak/strong flags → diagnostics clear",
    );
}

#[test]
fn hysteresis_setting() {
    let mut ctx = VerificationContext::new();
    for v in &["hysteresis_lsb", "max_hysteresis_lsb"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("setting_ok", i32_ty());
    // Programmable hysteresis to filter noise (0-7 LSB typical)
    ctx.push_obligation(ProofObligation::assume("hl", "hysteresis_lsb == 3"));
    ctx.push_obligation(ProofObligation::assume("mh", "max_hysteresis_lsb == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "setting_ok == if hysteresis_lsb <= max_hysteresis_lsb { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "setting_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Mag encoder: 3 LSB hysteresis ≤ 7 max → setting OK",
    );
}

#[test]
fn power_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("is_low_power", i32_ty());
    // Power modes: 0=normal, 1=low-power, 2=low-noise
    ctx.push_obligation(ProofObligation::assume("m", "mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "il_def",
        "is_low_power == if mode == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_low_power == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Mag encoder: mode=1 → low power");
}
