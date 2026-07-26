// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_vane_motor_displacement_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("displacement", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disp_range",
        "displacement >= 10 && displacement <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("disp_val", "displacement == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "disp_check",
        "displacement >= 10 && displacement <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement 300 (30.0 cc/rev) within [10,5000]");
}

#[test]
fn test_vane_motor_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "max_pressure >= 50 && max_pressure <= 350",
    ));
    ctx.push_obligation(ProofObligation::assume("press_val", "max_pressure == 210"));
    ctx.push_obligation(ProofObligation::assert(
        "press_check",
        "max_pressure >= 50 && max_pressure <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure 210 bar within [50,350]");
}

#[test]
fn test_vane_motor_max_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "max_speed >= 100 && max_speed <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "max_speed == 2400"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_check",
        "max_speed >= 100 && max_speed <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max speed 2400 RPM within [100,4000]");
}

#[test]
fn test_vane_motor_torque_output_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "torque_range",
        "torque >= 10 && torque <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("torque_val", "torque == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "torque_check",
        "torque >= 10 && torque <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "torque 1000 (100.0 Nm) within [10,50000]");
}

#[test]
fn test_vane_motor_number_of_vanes_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vanes", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vanes_range",
        "vanes >= 4 && vanes <= 16",
    ));
    ctx.push_obligation(ProofObligation::assume("vanes_val", "vanes == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "vanes_check",
        "vanes >= 4 && vanes <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 vanes within [4,16]");
}

#[test]
fn test_vane_motor_mechanical_efficiency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("efficiency", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eff_range",
        "efficiency >= 700 && efficiency <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("eff_val", "efficiency == 900"));
    ctx.push_obligation(ProofObligation::assert(
        "eff_check",
        "efficiency >= 700 && efficiency <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "efficiency 900 (90.0%) within [700,1000]");
}

#[test]
fn test_vane_motor_vane_material_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "material == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "mat_check",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "material 3 (steel) is valid enum {1=carbon,2=phenolic,3=steel}",
    );
}

#[test]
fn test_vane_motor_mounting_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mounting", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mount_val", "mounting == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "mount_check",
        "mounting == 1 || mounting == 2 || mounting == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mounting 2 (flange) is valid enum {1=foot,2=flange,3=cradle}",
    );
}

#[test]
fn test_vane_motor_rotation_direction_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotation", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rot_val", "rotation == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "rot_check",
        "rotation == 1 || rotation == 2 || rotation == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotation 3 (bidirectional) is valid enum {1=cw,2=ccw,3=bi}",
    );
}

#[test]
fn test_vane_motor_auto_speed_regulation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "reg_check",
        "(if flag == 1 { 1 } else { 0 }) == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto speed regulation active when flag==1");
}
