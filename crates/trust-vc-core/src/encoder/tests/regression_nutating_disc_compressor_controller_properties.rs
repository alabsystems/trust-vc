// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Disc wobble angle (x100 degrees) — bounded [100, 4500].
/// 100 represents 1.00 deg, 4500 represents 45.00 deg.
#[test]
fn test_nutating_disc_wobble_angle_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ang_a",
        "angle_x100 >= 100 && angle_x100 <= 4500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ang_c",
        "angle_x100 >= 100 && angle_x100 <= 4500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wobble angle x100 in [100, 4500] representing 1.00-45.00 degrees",
    );
}

/// Test 2: Shaft speed (RPM) — bounded [300, 10000].
#[test]
fn test_nutating_disc_shaft_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spd_a",
        "speed_rpm >= 300 && speed_rpm <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spd_c",
        "speed_rpm >= 300 && speed_rpm <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shaft speed in [300, 10000] RPM");
}

/// Test 3: Discharge pressure (x10 bar) — bounded [10, 2000].
/// 10 represents 1.0 bar, 2000 represents 200.0 bar.
#[test]
fn test_nutating_disc_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "disc_x10 >= 10 && disc_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "disc_x10 >= 10 && disc_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 in [10, 2000] representing 1.0-200.0 bar",
    );
}

/// Test 4: Disc diameter (mm) — bounded [20, 500].
#[test]
fn test_nutating_disc_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diam_mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dd_a",
        "diam_mm >= 20 && diam_mm <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dd_c",
        "diam_mm >= 20 && diam_mm <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "disc diameter in [20, 500] mm");
}

/// Test 5: Axial clearance (x10000 mm) — bounded [5, 2000].
/// 5 represents 0.0005 mm, 2000 represents 0.2000 mm.
#[test]
fn test_nutating_disc_axial_clearance_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("clr_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "clr_a",
        "clr_x10000 >= 5 && clr_x10000 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "clr_c",
        "clr_x10000 >= 5 && clr_x10000 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "axial clearance x10000 in [5, 2000] representing 0.0005-0.2000 mm",
    );
}

/// Test 6: Motor torque (x100 Nm) — bounded [1, 50000].
/// 1 represents 0.01 Nm, 50000 represents 500.00 Nm.
#[test]
fn test_nutating_disc_motor_torque_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tq_a",
        "torque_x100 >= 1 && torque_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tq_c",
        "torque_x100 >= 1 && torque_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motor torque x100 in [1, 50000] representing 0.01-500.00 Nm",
    );
}

/// Test 7: Disc material — 3-way disjunction.
/// 1=steel, 2=aluminum, 3=composite.
#[test]
fn test_nutating_disc_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_a",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("mat_c", "mat >= 1 && mat <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "disc material 3-way (steel/aluminum/composite)");
}

/// Test 8: Seal configuration — 3-way disjunction.
/// 1=face-seal, 2=labyrinth, 3=lip-seal.
#[test]
fn test_nutating_disc_seal_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "seal_a",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("seal_c", "seal >= 1 && seal <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "seal config 3-way (face-seal/labyrinth/lip-seal)");
}

/// Test 9: Working fluid — 3-way disjunction.
/// 1=air, 2=refrigerant, 3=process-gas.
#[test]
fn test_nutating_disc_working_fluid_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fluid", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fluid_a",
        "fluid == 1 || fluid == 2 || fluid == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fluid_c",
        "fluid >= 1 && fluid <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "working fluid 3-way (air/refrigerant/process-gas)");
}

/// Test 10: Oil-free operation flag — boolean.
/// 0=oil-lubricated, 1=oil-free.
#[test]
fn test_nutating_disc_oil_free_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "oil-free operation flag is boolean (0 or 1)");
}
