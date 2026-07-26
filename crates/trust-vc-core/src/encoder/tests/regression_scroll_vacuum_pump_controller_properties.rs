// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_scroll_vacuum_ultimate_pressure_mbar_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ult_p_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "up_a",
        "ult_p_x1000 >= 1 && ult_p_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "up_c",
        "ult_p_x1000 >= 1 && ult_p_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ultimate pressure x1000 in [1, 10000] representing 0.001-10.000 mbar",
    );
}

#[test]
fn test_scroll_vacuum_pumping_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_lpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ps_a",
        "speed_lpm >= 1 && speed_lpm <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ps_c",
        "speed_lpm >= 1 && speed_lpm <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pumping speed in [1, 2000] L/min");
}

#[test]
fn test_scroll_vacuum_motor_speed_rpm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ms_a",
        "motor_rpm >= 100 && motor_rpm <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ms_c",
        "motor_rpm >= 100 && motor_rpm <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor speed in [100, 5000] RPM");
}

#[test]
fn test_scroll_vacuum_tip_seal_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "seal_temp >= 10 && seal_temp <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "seal_temp >= 10 && seal_temp <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tip seal temperature in [10, 200] C");
}

#[test]
fn test_scroll_vacuum_power_consumption_w_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_w", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pw_a",
        "power_w >= 10 && power_w <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pw_c",
        "power_w >= 10 && power_w <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power consumption in [10, 5000] W");
}

#[test]
fn test_scroll_vacuum_orbit_radius_um_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("orbit_um", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "or_a",
        "orbit_um >= 100 && orbit_um <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "or_c",
        "orbit_um >= 100 && orbit_um <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "orbit radius in [100, 10000] um");
}

#[test]
fn test_scroll_vacuum_seal_material_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sm_a",
        "seal_mat == 1 || seal_mat == 2 || seal_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sm_c",
        "seal_mat == 1 || seal_mat == 2 || seal_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "seal material: PTFE, PEEK, or Vespel");
}

#[test]
fn test_scroll_vacuum_cooling_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cl_a",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cl_c",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling: air-cooled, water-cooled, or thermoelectric",
    );
}

#[test]
fn test_scroll_vacuum_gas_ballast_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ballast", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gb_a",
        "ballast == 1 || ballast == 2 || ballast == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gb_c",
        "ballast == 1 || ballast == 2 || ballast == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas ballast: off, low flow, or high flow");
}

#[test]
fn test_scroll_vacuum_inverter_drive_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inverter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "id_a",
        "inverter == 0 || inverter == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "id_c",
        "inverter == 0 || inverter == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inverter drive flag is boolean");
}
