// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_mag_pump_flow_rate_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "specific_flow",
        "flow_rate_x10 == 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_in_bounds",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate 50.0 L/min (x10 scaled) within valid range 0.1-1000.0",
    );
}

#[test]
fn test_mag_pump_max_head_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_head_m", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "head_range",
        "max_head_m >= 1 && max_head_m <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("specific_head", "max_head_m == 75"));
    ctx.push_obligation(ProofObligation::assert(
        "head_in_bounds",
        "max_head_m >= 1 && max_head_m <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max head 75 meters within valid range 1-200 m");
}

#[test]
fn test_mag_pump_motor_power_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_power_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "motor_power_x10 >= 1 && motor_power_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "specific_power",
        "motor_power_x10 == 1100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_in_bounds",
        "motor_power_x10 >= 1 && motor_power_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motor power 110.0 kW (x10 scaled) within valid range 0.1-500.0 kW",
    );
}

#[test]
fn test_mag_pump_coupling_torque_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "torque_range",
        "torque_x10 >= 10 && torque_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "specific_torque",
        "torque_x10 == 850",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "torque_in_bounds",
        "torque_x10 >= 10 && torque_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "magnet coupling torque 85.0 Nm (x10 scaled) within valid range 1.0-500.0 Nm",
    );
}

#[test]
fn test_mag_pump_max_temperature_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_temp_c", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "max_temp_c >= 20 && max_temp_c <= 400",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "specific_temp",
        "max_temp_c == 260",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_bounds",
        "max_temp_c >= 20 && max_temp_c <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max temperature 260 C within valid range 20-400 C");
}

#[test]
fn test_mag_pump_containment_shell_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shell_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "material_range",
        "shell_material >= 1 && shell_material <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "shell_material == 1 || shell_material == 2 || shell_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "containment shell material is one of hastelloy(1), PEEK(2), or silicon-carbide(3)",
    );
}

#[test]
fn test_mag_pump_magnet_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("magnet_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "magnet_range",
        "magnet_type >= 1 && magnet_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_magnet",
        "magnet_type == 1 || magnet_type == 2 || magnet_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "magnet type is one of rare-earth(1), samarium-cobalt(2), or ceramic(3)",
    );
}

#[test]
fn test_mag_pump_bearing_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bearing_range",
        "bearing_type >= 1 && bearing_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_bearing",
        "bearing_type == 1 || bearing_type == 2 || bearing_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bearing type is one of SiC(1), carbon(2), or PTFE(3)",
    );
}

#[test]
fn test_mag_pump_impeller_style() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impeller_style", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "impeller_range",
        "impeller_style >= 1 && impeller_style <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_impeller",
        "impeller_style == 1 || impeller_style == 2 || impeller_style == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impeller style is one of closed(1), semi-open(2), or open(3)",
    );
}

#[test]
fn test_mag_pump_dry_run_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dry_run_protection", i32_ty());
    ctx.declare_var_typed("pump_running", i32_ty());
    ctx.declare_var_typed("flow_detected", i32_ty());
    ctx.declare_var_typed("shutdown", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "protection_enabled",
        "dry_run_protection == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("pump_on", "pump_running == 1"));
    ctx.push_obligation(ProofObligation::assume("no_flow", "flow_detected == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "shutdown_def",
        "shutdown == if dry_run_protection == 1 { if pump_running == 1 && flow_detected == 0 { 1 } else { 0 } } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "triggers_shutdown",
        "shutdown == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dry run protection triggers shutdown when pump running with no flow detected",
    );
}
