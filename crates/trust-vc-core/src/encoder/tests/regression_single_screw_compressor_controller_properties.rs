// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_single_screw_compressor_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_press_range",
        "press_x10 >= 20 && press_x10 <= 160",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_press_range",
        "press_x10 >= 20 && press_x10 <= 160",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 bounded 0.1 bar (2.0-16.0 bar)",
    );
}

#[test]
fn test_single_screw_compressor_main_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_speed_range",
        "speed >= 500 && speed <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_speed_range",
        "speed >= 500 && speed <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "main rotor speed bounded 500-6000 RPM");
}

#[test]
fn test_single_screw_compressor_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_flow_range",
        "flow_x10 >= 10 && flow_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_flow_range",
        "flow_x10 >= 10 && flow_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate x10 bounded 0.1 m3/min (1.0-500.0 m3/min)",
    );
}

#[test]
fn test_single_screw_compressor_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_power_range",
        "power >= 5 && power <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_power_range",
        "power >= 5 && power <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power bounded 5-1000 kW");
}

#[test]
fn test_single_screw_compressor_discharge_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_temp_range",
        "temp_off >= 150 && temp_off <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_temp_range",
        "temp_off >= 150 && temp_off <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge temp offset+100 bounded (50-250 C)");
}

#[test]
fn test_single_screw_compressor_gate_rotor_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_gate_material",
        "gm == 1 || gm == 2 || gm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_gate_material",
        "gm == 1 || gm == 2 || gm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gate rotor material three-way: 1=composite, 2=aluminum, 3=steel",
    );
}

#[test]
fn test_single_screw_compressor_lubrication_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lub", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_lubrication",
        "lub == 1 || lub == 2 || lub == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_lubrication",
        "lub == 1 || lub == 2 || lub == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lubrication three-way: 1=oil-flooded, 2=oil-free, 3=water-injected",
    );
}

#[test]
fn test_single_screw_compressor_capacity_control_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_capacity_control",
        "cc == 1 || cc == 2 || cc == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_capacity_control",
        "cc == 1 || cc == 2 || cc == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capacity control three-way: 1=slide-valve, 2=VFD, 3=suction-throttle",
    );
}

#[test]
fn test_single_screw_compressor_auto_oil_temp_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_oil_temp_flag",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_oil_temp_flag",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto oil temp flag boolean (0 or 1)");
}

#[test]
fn test_single_screw_compressor_compression_ratio_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_ratio_range",
        "ratio_x10 >= 15 && ratio_x10 <= 80",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_ratio_range",
        "ratio_x10 >= 15 && ratio_x10 <= 80",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "compression ratio x10 bounded 0.1 (1.5-8.0)");
}
