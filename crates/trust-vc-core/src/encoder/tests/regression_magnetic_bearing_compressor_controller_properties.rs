// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_magnetic_bearing_compressor_shaft_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 10000 && speed <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 10000 && speed <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shaft speed must be between 10000 and 100000 RPM");
}

#[test]
fn test_magnetic_bearing_compressor_stiffness_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stiff_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stiff_range",
        "stiff_x10 >= 10 && stiff_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stiff_bounded",
        "stiff_x10 >= 10 && stiff_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bearing stiffness x10 must be in range 10-10000 representing 1.0-1000.0 N/um",
    );
}

#[test]
fn test_magnetic_bearing_compressor_clearance_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("clear_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "clear_range",
        "clear_x100 >= 10 && clear_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "clear_bounded",
        "clear_x100 >= 10 && clear_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "radial clearance x100 must be in range 10-5000 representing 0.10-50.00 um",
    );
}

#[test]
fn test_magnetic_bearing_compressor_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power >= 10 && power <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power >= 10 && power <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power must be between 10 and 5000 kW");
}

#[test]
fn test_magnetic_bearing_compressor_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 10 && press_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press_x10 >= 10 && press_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 must be in range 10-200 representing 1.0-20.0 bar",
    );
}

#[test]
fn test_magnetic_bearing_compressor_axes_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("axes", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "axes_range",
        "axes >= 3 && axes <= 5",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "axes_bounded",
        "axes >= 3 && axes <= 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of bearing axes must be between 3 and 5");
}

#[test]
fn test_magnetic_bearing_compressor_bearing_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("btype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "btype_range",
        "btype == 1 || btype == 2 || btype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "btype_valid",
        "btype == 1 || btype == 2 || btype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bearing type must be active-radial (1), active-axial (2), or hybrid (3)",
    );
}

#[test]
fn test_magnetic_bearing_compressor_control_algorithm_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("algo", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "algo_range",
        "algo == 1 || algo == 2 || algo == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "algo_valid",
        "algo == 1 || algo == 2 || algo == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "control algorithm must be PID (1), LQR (2), or mu-synthesis (3)",
    );
}

#[test]
fn test_magnetic_bearing_compressor_backup_system_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("backup", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "backup_range",
        "backup == 1 || backup == 2 || backup == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "backup_valid",
        "backup == 1 || backup == 2 || backup == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "backup system must be touchdown-bearing (1), auxiliary-bearing (2), or catcher-bearing (3)");
}

#[test]
fn test_magnetic_bearing_compressor_auto_levitation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lev", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lev_range", "lev == 0 || lev == 1"));
    ctx.push_obligation(ProofObligation::assert("lev_valid", "lev == 0 || lev == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic levitation control flag must be 0 (disabled) or 1 (enabled)",
    );
}
