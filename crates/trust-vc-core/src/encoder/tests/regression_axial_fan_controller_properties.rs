// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_axial_fan_airflow_scaled_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "airflow_range",
        "flow_x10 > 0 && flow_x10 < 5000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "airflow_positive",
        "flow_x10 >= 1 && flow_x10 <= 4999999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "airflow x10 m3/h in (0, 5000000) implies [1, 4999999]",
    );
}

#[test]
fn test_axial_fan_total_pressure_scaled_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "press_x10 > 0 && press_x10 < 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_positive",
        "press_x10 >= 1 && press_x10 <= 49999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "total pressure x10 Pa in (0, 50000) implies [1, 49999]",
    );
}

#[test]
fn test_axial_fan_diameter_scaled_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diam_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diameter_range",
        "diam_x10 > 0 && diam_x10 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diameter_positive",
        "diam_x10 >= 1 && diam_x10 <= 99999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fan diameter x10 mm in (0, 100000) implies [1, 99999]",
    );
}

#[test]
fn test_axial_fan_blade_pitch_angle_scaled_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pitch_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pitch_range",
        "pitch_x10 > 0 && pitch_x10 < 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pitch_positive",
        "pitch_x10 >= 1 && pitch_x10 <= 899",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "blade pitch x10 degrees in (0, 900) implies [1, 899]",
    );
}

#[test]
fn test_axial_fan_rotation_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 100 && rpm <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_positive",
        "rpm > 0 && rpm <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotation speed in [100, 5000] RPM implies positive and bounded",
    );
}

#[test]
fn test_axial_fan_number_of_blades_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blades", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "blades_range",
        "blades >= 2 && blades <= 24",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "blades_valid",
        "blades > 0 && blades <= 24",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "blade count in [2, 24] implies positive and bounded",
    );
}

#[test]
fn test_axial_fan_blade_profile_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("profile", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "profile_valid",
        "profile == 1 || profile == 2 || profile == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "profile_in_range",
        "profile >= 1 && profile <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "blade profile 1=flat 2=airfoil 3=twisted implies [1, 3]",
    );
}

#[test]
fn test_axial_fan_mounting_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mount", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mount_valid",
        "mount == 1 || mount == 2 || mount == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mount_in_range",
        "mount >= 1 && mount <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mounting type 1=wall 2=duct 3=roof implies [1, 3]");
}

#[test]
fn test_axial_fan_speed_control_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ctrl_valid",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ctrl_in_range",
        "ctrl >= 1 && ctrl <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "speed control 1=VFD 2=pole-switching 3=pitch-adjustment implies [1, 3]",
    );
}

#[test]
fn test_axial_fan_automatic_stall_detection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stall_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "boolean_flag",
        "stall_flag == 0 || stall_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded",
        "stall_flag >= 0 && stall_flag <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "stall detection boolean flag 0 or 1 implies [0, 1]",
    );
}
