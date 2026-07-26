// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_oil_flooded_screw_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotor_speed_rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rotor_speed_range",
        "rotor_speed_rpm >= 500 && rotor_speed_rpm <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rotor_speed_bounded",
        "rotor_speed_rpm >= 500 && rotor_speed_rpm <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed stays within 500-6000 RPM");
}

#[test]
fn test_oil_flooded_screw_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_pressure_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discharge_pressure_range",
        "discharge_pressure_x10 >= 50 && discharge_pressure_x10 <= 160",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discharge_pressure_x10_bounded",
        "discharge_pressure_x10 >= 50 && discharge_pressure_x10 <= 160",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 stays within 50-160 (5.0-16.0 bar)",
    );
}

#[test]
fn test_oil_flooded_screw_oil_injection_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_injection_temp_offset100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oil_injection_temp_range",
        "oil_injection_temp_offset100 >= 140 && oil_injection_temp_offset100 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oil_injection_temp_offset100_bounded",
        "oil_injection_temp_offset100 >= 140 && oil_injection_temp_offset100 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "oil injection temp offset+100 stays within 140-200 (40-100 C)",
    );
}

#[test]
fn test_oil_flooded_screw_free_air_delivery_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("free_air_delivery_lpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "free_air_delivery_range",
        "free_air_delivery_lpm >= 10 && free_air_delivery_lpm <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "free_air_delivery_bounded",
        "free_air_delivery_lpm >= 10 && free_air_delivery_lpm <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "free air delivery stays within 10-100000 L/min");
}

#[test]
fn test_oil_flooded_screw_oil_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_flow_rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oil_flow_rate_range",
        "oil_flow_rate_x10 >= 10 && oil_flow_rate_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oil_flow_rate_x10_bounded",
        "oil_flow_rate_x10 >= 10 && oil_flow_rate_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "oil flow rate x10 stays within 10-5000 (1.0-500.0 L/min)",
    );
}

#[test]
fn test_oil_flooded_screw_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_power_kw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "motor_power_range",
        "motor_power_kw >= 1 && motor_power_kw <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "motor_power_bounded",
        "motor_power_kw >= 1 && motor_power_kw <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power stays within 1-1000 kW");
}

#[test]
fn test_oil_flooded_screw_oil_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oil_type_range",
        "oil_type >= 1 && oil_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oil_type_valid",
        "oil_type >= 1 && oil_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "oil type is 1=mineral, 2=synthetic-PAO, or 3=synthetic-ester",
    );
}

#[test]
fn test_oil_flooded_screw_separator_element_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("separator_element", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "separator_element_range",
        "separator_element >= 1 && separator_element <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "separator_element_valid",
        "separator_element >= 1 && separator_element <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "separator element is 1=coalescing, 2=centrifugal, or 3=multi-stage",
    );
}

#[test]
fn test_oil_flooded_screw_capacity_regulation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity_regulation", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "capacity_regulation_range",
        "capacity_regulation >= 1 && capacity_regulation <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "capacity_regulation_valid",
        "capacity_regulation >= 1 && capacity_regulation <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capacity regulation is 1=inlet-valve, 2=slide-valve, or 3=VSD",
    );
}

#[test]
fn test_oil_flooded_screw_auto_oil_level_monitor_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_oil_level_monitor", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_oil_level_monitor_range",
        "auto_oil_level_monitor >= 0 && auto_oil_level_monitor <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_oil_level_monitor_valid",
        "auto_oil_level_monitor >= 0 && auto_oil_level_monitor <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto oil level monitor flag is 0=disabled or 1=enabled",
    );
}
