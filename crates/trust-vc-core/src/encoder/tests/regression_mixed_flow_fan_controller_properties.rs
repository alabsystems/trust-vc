// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Mixed flow fan controller property verification tests

use super::*;

#[test]
fn test_mixed_flow_fan_airflow_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "airflow_bounds",
        "flow_x10 > 0 && flow_x10 < 2000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "airflow_positive_and_bounded",
        "flow_x10 >= 1 && flow_x10 <= 1999999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "airflow scaled by x10 m3/h must be within valid range",
    );
}

#[test]
fn test_mixed_flow_fan_total_pressure_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_bounds",
        "press_x10 > 0 && press_x10 < 80000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_positive_and_bounded",
        "press_x10 >= 1 && press_x10 <= 79999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "total pressure scaled by x10 Pa must be within valid range",
    );
}

#[test]
fn test_mixed_flow_fan_impeller_diameter_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diam_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diameter_bounds",
        "diam_x10 > 0 && diam_x10 < 60000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diameter_positive_and_bounded",
        "diam_x10 >= 1 && diam_x10 <= 59999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impeller diameter scaled by x10 mm must be within valid range",
    );
}

#[test]
fn test_mixed_flow_fan_cone_angle_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cone_angle_bounds",
        "angle_x10 > 0 && angle_x10 < 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cone_angle_positive_and_bounded",
        "angle_x10 >= 1 && angle_x10 <= 899",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cone angle scaled by x10 degrees must be within valid range",
    );
}

#[test]
fn test_mixed_flow_fan_rotation_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_bounds",
        "rpm >= 100 && rpm <= 8000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_in_operating_range",
        "rpm > 0 && rpm < 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotation speed must be within 100-8000 RPM operating range",
    );
}

#[test]
fn test_mixed_flow_fan_blade_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blades", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "blade_bounds",
        "blades >= 4 && blades <= 32",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "blade_count_valid",
        "blades > 0 && blades < 64",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of blades must be within 4-32 range");
}

#[test]
fn test_mixed_flow_fan_impeller_design_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("design", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "design_type",
        "design == 1 || design == 2 || design == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "design_is_valid_variant",
        "design >= 1 && design <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impeller design must be swept-back(1), radial-tip(2), or forward-swept(3)",
    );
}

#[test]
fn test_mixed_flow_fan_diffuser_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diffuser", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diffuser_type",
        "diffuser == 1 || diffuser == 2 || diffuser == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diffuser_is_valid_variant",
        "diffuser >= 1 && diffuser <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "diffuser type must be vaned(1), vaneless(2), or conical(3)",
    );
}

#[test]
fn test_mixed_flow_fan_motor_integration_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "motor_type",
        "motor == 1 || motor == 2 || motor == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "motor_is_valid_variant",
        "motor >= 1 && motor <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motor integration must be direct-drive(1), belt-drive(2), or hub-motor(3)",
    );
}

#[test]
fn test_mixed_flow_fan_anti_vibration_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("anti_vib", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "boolean_flag",
        "anti_vib == 0 || anti_vib == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_is_boolean",
        "anti_vib >= 0 && anti_vib <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "anti-vibration control flag must be boolean (0 or 1)",
    );
}
