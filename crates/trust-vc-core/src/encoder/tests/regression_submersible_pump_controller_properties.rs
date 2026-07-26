// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_rate_scaled_bounded() {
    // Flow rate in ×10 m³/h (0.1 m³/h resolution): 1 to 5000 (0.1 to 500.0 m³/h)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate_x10 == 250")); // 25.0 m³/h
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if flow_rate_x10 >= 1 && flow_rate_x10 <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pump flow: 25.0 m³/h (×10=250) in [1, 5000]");
}

#[test]
fn head_bounded() {
    // Total dynamic head in meters: 5 to 500
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head_m", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("h", "head_m == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if head_m >= 5 && head_m <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pump head: 120m in [5, 500]");
}

#[test]
fn motor_power_bounded() {
    // Motor power in kW: 1 to 500
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_kw", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pw", "power_kw == 75"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if power_kw >= 1 && power_kw <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power: 75kW in [1, 500]");
}

#[test]
fn impeller_stages_bounded() {
    // Number of impeller stages: 1 to 20
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "stages == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if stages >= 1 && stages <= 20 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller stages: 8 in [1, 20]");
}

#[test]
fn submersion_depth_bounded() {
    // Submersion depth in meters: 5 to 300
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_m", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "depth_m == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if depth_m >= 5 && depth_m <= 300 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "submersion depth: 150m in [5, 300]");
}

#[test]
fn pump_type_three_way_disjunction() {
    // Pump type: 1=centrifugal, 2=mixed flow, 3=axial flow
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pt", "pump_type == 2")); // mixed flow
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "pump_type == 1 || pump_type == 2 || pump_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pump type: 2 (mixed flow) in {1,2,3}");
}

#[test]
fn cable_type_three_way_disjunction() {
    // Cable type: 1=flat, 2=round, 3=armored
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cable_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ct", "cable_type == 3")); // armored
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "cable_type == 1 || cable_type == 2 || cable_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cable type: 3 (armored) in {1,2,3}");
}

#[test]
fn efficiency_scaled_bounded() {
    // Efficiency in ×10 % (0.1% resolution): 300 to 950 (30.0% to 95.0%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("efficiency_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("eff", "efficiency_x10 == 780")); // 78.0%
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if efficiency_x10 >= 300 && efficiency_x10 <= 950 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pump efficiency: 78.0% (×10=780) in [300, 950]");
}

#[test]
fn motor_voltage_bounded() {
    // Motor voltage in V: 220 to 6600
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_v", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("v", "voltage_v == 460"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if voltage_v >= 220 && voltage_v <= 6600 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor voltage: 460V in [220, 6600]");
}

#[test]
fn thermal_protection_boolean_flag() {
    // Thermal protection: i32 flag (1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_temp_c", u32_ty());
    ctx.declare_var_typed("temp_limit_c", u32_ty());
    ctx.declare_var_typed("thermal_prot", i32_ty());
    ctx.declare_var_typed("shutdown", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mt", "motor_temp_c == 95"));
    ctx.push_obligation(ProofObligation::assume("tl", "temp_limit_c == 90"));
    ctx.push_obligation(ProofObligation::assume("tp", "thermal_prot == 1")); // enabled
    ctx.push_obligation(ProofObligation::assume(
        "sd_def",
        "shutdown == if thermal_prot == 1 { if motor_temp_c > temp_limit_c { 1 } else { 0 } } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "shutdown == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thermal protection: 95C > 90C limit, enabled -> shutdown",
    );
}
