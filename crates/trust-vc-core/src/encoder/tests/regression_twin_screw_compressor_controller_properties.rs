// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_twin_screw_compressor_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotor_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rotor_speed_range",
        "rotor_speed >= 500 && rotor_speed <= 15000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rotor_speed_bounded",
        "rotor_speed >= 500 && rotor_speed <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed must be between 500 and 15000 RPM");
}

#[test]
fn test_twin_screw_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discharge_pressure_range",
        "discharge_pressure >= 2 && discharge_pressure <= 40",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discharge_pressure_bounded",
        "discharge_pressure >= 2 && discharge_pressure <= 40",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure must be between 2 and 40 bar");
}

#[test]
fn test_twin_screw_compressor_suction_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("suction_pressure_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "suction_pressure_x10_range",
        "suction_pressure_x10 >= 5 && suction_pressure_x10 <= 150",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "suction_pressure_x10_bounded",
        "suction_pressure_x10 >= 5 && suction_pressure_x10 <= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "suction pressure x10 must be between 5 and 150 (0.5-15.0 bar)",
    );
}

#[test]
fn test_twin_screw_compressor_oil_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_temp_offset100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oil_temp_offset100_range",
        "oil_temp_offset100 >= 80 && oil_temp_offset100 <= 250",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oil_temp_offset100_bounded",
        "oil_temp_offset100 >= 80 && oil_temp_offset100 <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "oil temperature offset+100 must be between 80 and 250 (-20 to 150 C)",
    );
}

#[test]
fn test_twin_screw_compressor_volume_ratio_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume_ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "volume_ratio_x10_range",
        "volume_ratio_x10 >= 20 && volume_ratio_x10 <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "volume_ratio_x10_bounded",
        "volume_ratio_x10 >= 20 && volume_ratio_x10 <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "volume ratio x10 must be between 20 and 60 (2.0-6.0)",
    );
}

#[test]
fn test_twin_screw_compressor_power_consumption_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_consumption", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_consumption_range",
        "power_consumption >= 5 && power_consumption <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_consumption_bounded",
        "power_consumption >= 5 && power_consumption <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power consumption must be between 5 and 5000 kW");
}

#[test]
fn test_twin_screw_compressor_rotor_profile_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotor_profile", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rotor_profile_range",
        "rotor_profile >= 1 && rotor_profile <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rotor_profile_valid",
        "rotor_profile == 1 || rotor_profile == 2 || rotor_profile == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotor profile must be 1=symmetric, 2=asymmetric, or 3=variable-pitch",
    );
}

#[test]
fn test_twin_screw_compressor_oil_injection_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_injection", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oil_injection_range",
        "oil_injection >= 1 && oil_injection <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oil_injection_valid",
        "oil_injection == 1 || oil_injection == 2 || oil_injection == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "oil injection must be 1=flooded, 2=oil-free, or 3=water-injected",
    );
}

#[test]
fn test_twin_screw_compressor_capacity_control_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity_control", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "capacity_control_range",
        "capacity_control >= 1 && capacity_control <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "capacity_control_valid",
        "capacity_control == 1 || capacity_control == 2 || capacity_control == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capacity control must be 1=slide-valve, 2=variable-speed, or 3=suction-throttle",
    );
}

#[test]
fn test_twin_screw_compressor_auto_dual_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_dual_control", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_dual_control_range",
        "auto_dual_control >= 0 && auto_dual_control <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_dual_control_valid",
        "auto_dual_control == 0 || auto_dual_control == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto dual control flag must be 0=disabled or 1=enabled",
    );
}
