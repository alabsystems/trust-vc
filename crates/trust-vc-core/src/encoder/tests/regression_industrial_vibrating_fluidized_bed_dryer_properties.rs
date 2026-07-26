// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial vibrating fluidized bed dryer property verification.
// Encodes key parameters of an industrial vibrating fluidized bed dryer system
// and verifies that they satisfy bounded, offset, scaled, disjunctive, and
// boolean-flag constraints.

/// Test 1: Vibration frequency (Hz) — bounded [5, 100], value 25.
#[test]
fn test_vibrating_fb_dryer_vibration_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vib_freq_hz", u32_ty());
    ctx.push_obligation(ProofObligation::assume("freq_val", "vib_freq_hz == 25"));
    ctx.push_obligation(ProofObligation::assert("freq_min", "vib_freq_hz >= 5"));
    ctx.push_obligation(ProofObligation::assert("freq_max", "vib_freq_hz <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vibration frequency 25 Hz in [5, 100]");
}

/// Test 2: Bed temperature offset +100 (deg C) — bounded via range assumption.
/// Offset encoding: temp_off = actual_temp + 100. Assume temp_off in (100, 800),
/// assert it stays within [101, 799].
#[test]
fn test_vibrating_fb_dryer_bed_temperature_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off > 100 && temp_off < 800",
    ));
    ctx.push_obligation(ProofObligation::assert("temp_lo", "temp_off >= 101"));
    ctx.push_obligation(ProofObligation::assert("temp_hi", "temp_off <= 799"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bed temperature offset in (100, 800) implies [101, 799]",
    );
}

/// Test 3: Air velocity (x10 m/s) — scaled at 0.1 m/s, assume in (0, 500),
/// assert stays within [1, 499].
#[test]
fn test_vibrating_fb_dryer_air_velocity_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vel_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vel_range",
        "vel_x10 > 0 && vel_x10 < 500",
    ));
    ctx.push_obligation(ProofObligation::assert("vel_lo", "vel_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("vel_hi", "vel_x10 <= 499"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air velocity x10 in (0, 500) implies [1, 499]");
}

/// Test 4: Bed depth (x10 mm) — scaled at 0.1 mm, assume in (0, 5000),
/// assert stays within [1, 4999].
#[test]
fn test_vibrating_fb_dryer_bed_depth_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "depth_range",
        "depth_x10 > 0 && depth_x10 < 5000",
    ));
    ctx.push_obligation(ProofObligation::assert("depth_lo", "depth_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("depth_hi", "depth_x10 <= 4999"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bed depth x10 in (0, 5000) implies [1, 4999]");
}

/// Test 5: Particle retention time (x100 sec) — scaled at 0.01 sec, assume
/// in (0, 100000), assert stays within [1, 99999].
#[test]
fn test_vibrating_fb_dryer_particle_retention_time_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_range",
        "time_x100 > 0 && time_x100 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert("time_lo", "time_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert("time_hi", "time_x100 <= 99999"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "retention time x100 in (0, 100000) implies [1, 99999]",
    );
}

/// Test 6: Number of vibration motors — bounded [1, 8], value 4.
#[test]
fn test_vibrating_fb_dryer_motor_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("motor_val", "motor_count == 4"));
    ctx.push_obligation(ProofObligation::assert("motor_min", "motor_count >= 1"));
    ctx.push_obligation(ProofObligation::assert("motor_max", "motor_count <= 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vibration motor count 4 in [1, 8]");
}

/// Test 7: Vibration pattern — 3-way disjunction.
/// 1=circular, 2=linear, 3=elliptical. Value 2 (linear).
#[test]
fn test_vibrating_fb_dryer_vibration_pattern_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pattern", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pat_val", "pattern == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_pattern",
        "pattern == 1 || pattern == 2 || pattern == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vibration pattern 2 (linear) is valid 3-way disjunction",
    );
}

/// Test 8: Fluidization regime — 3-way disjunction.
/// 1=bubbling, 2=slugging, 3=turbulent. Value 1 (bubbling).
#[test]
fn test_vibrating_fb_dryer_fluidization_regime_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("regime", u32_ty());
    ctx.push_obligation(ProofObligation::assume("reg_val", "regime == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_regime",
        "regime == 1 || regime == 2 || regime == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fluidization regime 1 (bubbling) is valid 3-way disjunction",
    );
}

/// Test 9: Heat source — 3-way disjunction.
/// 1=steam, 2=hot-air, 3=thermal-oil. Value 3 (thermal-oil).
#[test]
fn test_vibrating_fb_dryer_heat_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", u32_ty());
    ctx.push_obligation(ProofObligation::assume("src_val", "source == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_source",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heat source 3 (thermal-oil) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic vibration amplitude control — boolean flag using i32
/// with if/else pattern. Flag 1 = amplitude auto-control enabled, amp_active = 1.
#[test]
fn test_vibrating_fb_dryer_auto_amplitude_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("amp_flag", i32_ty());
    ctx.declare_var_typed("amp_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "amp_flag == 0 || amp_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "amp_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "amp_def",
        "amp_active == if amp_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("amp_enabled", "amp_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto amplitude control flag activates vibration controller",
    );
}
