// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_archimedes_screw_pump_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 > 0 && flow_x10 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_positive",
        "flow_x10 >= 1 && flow_x10 <= 99999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate (x10 L/s) must be strictly within operational bounds",
    );
}

#[test]
fn test_archimedes_screw_pump_lift_height_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lift_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lift_range",
        "lift_x10 > 0 && lift_x10 < 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lift_positive",
        "lift_x10 >= 1 && lift_x10 <= 999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lift height (x10 m) must be strictly within operational bounds",
    );
}

#[test]
fn test_archimedes_screw_pump_screw_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diam_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diam_range",
        "diam_x10 > 0 && diam_x10 < 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diam_positive",
        "diam_x10 >= 1 && diam_x10 <= 49999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "screw diameter (x10 mm) must be strictly within operational bounds",
    );
}

#[test]
fn test_archimedes_screw_pump_inclination_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "angle_range",
        "angle_x10 > 0 && angle_x10 < 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "angle_valid",
        "angle_x10 >= 1 && angle_x10 <= 899",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inclination angle (x10 degrees) must be within 0-90 exclusive",
    );
}

#[test]
fn test_archimedes_screw_pump_rotation_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 1 && rpm <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_positive_and_bounded",
        "rpm > 0 && rpm <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed must be between 1 and 200 RPM");
}

#[test]
fn test_archimedes_screw_pump_number_of_flights_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flights", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flights_range",
        "flights >= 1 && flights <= 5",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flights_valid",
        "flights > 0 && flights < 6",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of flights must be between 1 and 5");
}

#[test]
fn test_archimedes_screw_pump_screw_material_disjunction() {
    // 1=stainless-steel, 2=carbon-steel, 3=composite
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_valid",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_in_range",
        "mat >= 1 && mat <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "screw material must be stainless-steel(1), carbon-steel(2), or composite(3)",
    );
}

#[test]
fn test_archimedes_screw_pump_trough_type_disjunction() {
    // 1=open, 2=enclosed, 3=U-shaped
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trough", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "trough_valid",
        "trough == 1 || trough == 2 || trough == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "trough_in_range",
        "trough >= 1 && trough <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trough type must be open(1), enclosed(2), or U-shaped(3)",
    );
}

#[test]
fn test_archimedes_screw_pump_drive_method_disjunction() {
    // 1=direct, 2=chain, 3=gear-motor
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drive_valid",
        "drive == 1 || drive == 2 || drive == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drive_in_range",
        "drive >= 1 && drive <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive method must be direct(1), chain(2), or gear-motor(3)",
    );
}

#[test]
fn test_archimedes_screw_pump_auto_speed_regulation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_reg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_boolean",
        "auto_reg == 0 || auto_reg == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded",
        "auto_reg >= 0 && auto_reg <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic speed regulation flag must be 0 (off) or 1 (on)",
    );
}
