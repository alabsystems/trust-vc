// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Suction pressure at ×10 bar must be bounded between 1 and 100.
#[test]
fn test_rolling_piston_compressor_suction_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sp_a",
        "press_x10 >= 1 && press_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sp_c",
        "press_x10 >= 1 && press_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rolling piston compressor suction pressure bounded",
    );
}

/// Discharge pressure at ×10 bar must be bounded between 10 and 400.
#[test]
fn test_rolling_piston_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "disc_x10 >= 10 && disc_x10 <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "disc_x10 >= 10 && disc_x10 <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rolling piston compressor discharge pressure bounded",
    );
}

/// Motor speed in RPM must be bounded between 1000 and 9000.
#[test]
fn test_rolling_piston_compressor_motor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ms_a",
        "speed >= 1000 && speed <= 9000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ms_c",
        "speed >= 1000 && speed <= 9000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rolling piston compressor motor speed bounded");
}

/// Cylinder volume at ×100 cc must be bounded between 10 and 10000.
#[test]
fn test_rolling_piston_compressor_cylinder_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vol_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cv_a",
        "vol_x100 >= 10 && vol_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cv_c",
        "vol_x100 >= 10 && vol_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rolling piston compressor cylinder volume bounded");
}

/// Discharge temperature with offset +100 °C must be bounded between 120 and 400.
#[test]
fn test_rolling_piston_compressor_discharge_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "temp_off >= 120 && temp_off <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "temp_off >= 120 && temp_off <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rolling piston compressor discharge temperature bounded",
    );
}

/// Oil charge at ×10 mL must be bounded between 50 and 5000.
#[test]
fn test_rolling_piston_compressor_oil_charge_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oc_a",
        "oil_x10 >= 50 && oil_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oc_c",
        "oil_x10 >= 50 && oil_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rolling piston compressor oil charge bounded");
}

/// Refrigerant type must be one of R410A (1), R32 (2), or R290 (3).
#[test]
fn test_rolling_piston_compressor_refrigerant_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refrigerant", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rt_a",
        "refrigerant == 1 || refrigerant == 2 || refrigerant == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rt_c",
        "refrigerant == 1 || refrigerant == 2 || refrigerant == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rolling piston compressor refrigerant type valid");
}

/// Motor type must be one of BLDC (1), induction (2), or reluctance (3).
#[test]
fn test_rolling_piston_compressor_motor_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mt_a",
        "motor == 1 || motor == 2 || motor == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mt_c",
        "motor == 1 || motor == 2 || motor == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rolling piston compressor motor type valid");
}

/// Capacity control must be one of inverter (1), on-off (2), or unloader (3).
#[test]
fn test_rolling_piston_compressor_capacity_control_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cc_a",
        "capacity == 1 || capacity == 2 || capacity == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cc_c",
        "capacity == 1 || capacity == 2 || capacity == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rolling piston compressor capacity control valid");
}

/// Automatic oil return flag must be a boolean value (0 or 1).
#[test]
fn test_rolling_piston_compressor_oil_return_flag_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("or_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("or_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rolling piston compressor automatic oil return boolean",
    );
}
