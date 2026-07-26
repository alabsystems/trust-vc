// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_rotary_lobe_compressor_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 500 && speed <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 500 && speed <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed must be between 500 and 5000 RPM");
}

#[test]
fn test_rotary_lobe_compressor_differential_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure_x10 >= 1 && pressure_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure_x10 >= 1 && pressure_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "differential pressure x10 must be between 1 and 10000 (0.1-1000.0 mbar)",
    );
}

#[test]
fn test_rotary_lobe_compressor_displacement_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("displacement_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "displacement_range",
        "displacement_x10 >= 10 && displacement_x10 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "displacement_bounded",
        "displacement_x10 >= 10 && displacement_x10 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "displacement x10 must be between 10 and 100000 (1.0-10000.0 m3/h)",
    );
}

#[test]
fn test_rotary_lobe_compressor_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_kw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power_kw >= 1 && power_kw <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power_kw >= 1 && power_kw <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power must be between 1 and 1000 kW");
}

#[test]
fn test_rotary_lobe_compressor_noise_level_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise_db", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "noise_range",
        "noise_db >= 60 && noise_db <= 110",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "noise_bounded",
        "noise_db >= 60 && noise_db <= 110",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "noise level must be between 60 and 110 dB");
}

#[test]
fn test_rotary_lobe_compressor_number_of_lobes_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lobes", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lobes_range",
        "lobes >= 2 && lobes <= 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lobes_bounded",
        "lobes >= 2 && lobes <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of lobes must be between 2 and 4");
}

#[test]
fn test_rotary_lobe_compressor_lobe_profile_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lobe_profile", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lobe_profile_valid",
        "lobe_profile == 1 || lobe_profile == 2 || lobe_profile == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lobe_profile_in_set",
        "lobe_profile == 1 || lobe_profile == 2 || lobe_profile == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lobe profile must be 1=straight, 2=helical, or 3=twisted",
    );
}

#[test]
fn test_rotary_lobe_compressor_sealing_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sealing_method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sealing_method_valid",
        "sealing_method == 1 || sealing_method == 2 || sealing_method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sealing_method_in_set",
        "sealing_method == 1 || sealing_method == 2 || sealing_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sealing method must be 1=clearance, 2=lip-seal, or 3=mechanical-seal",
    );
}

#[test]
fn test_rotary_lobe_compressor_drive_configuration_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_config", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drive_config_valid",
        "drive_config == 1 || drive_config == 2 || drive_config == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drive_config_in_set",
        "drive_config == 1 || drive_config == 2 || drive_config == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive configuration must be 1=belt, 2=direct, or 3=gear",
    );
}

#[test]
fn test_rotary_lobe_compressor_automatic_pressure_relief_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_relief", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_relief_bool",
        "pressure_relief == 0 || pressure_relief == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_relief_is_flag",
        "pressure_relief == 0 || pressure_relief == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic pressure relief flag must be 0 (disabled) or 1 (enabled)",
    );
}
