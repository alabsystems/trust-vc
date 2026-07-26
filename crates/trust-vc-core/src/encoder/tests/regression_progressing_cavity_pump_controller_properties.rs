// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Flow rate scaled x10 (L/min) must stay in valid operating range.
#[test]
fn test_progressing_cavity_pump_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 > 0 && flow_x10 < 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_positive_and_bounded",
        "flow_x10 >= 1 && flow_x10 <= 49999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 in (0, 50000) implies [1, 49999]");
}

/// Test 2: Maximum discharge pressure must be bounded (1-500 bar).
#[test]
fn test_progressing_cavity_pump_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure_bar >= 1 && pressure_bar <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_positive_and_bounded",
        "pressure_bar > 0 && pressure_bar <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pressure in [1, 500] bar implies positive and bounded",
    );
}

/// Test 3: Rotor speed must be bounded (1-1000 RPM).
#[test]
fn test_progressing_cavity_pump_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 1 && rpm <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_positive_and_bounded",
        "rpm > 0 && rpm <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotor speed in [1, 1000] RPM implies positive and bounded",
    );
}

/// Test 4: Number of stages must be bounded (1-12).
#[test]
fn test_progressing_cavity_pump_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stages_range",
        "stages >= 1 && stages <= 12",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stages_positive_and_bounded",
        "stages > 0 && stages <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "number of stages in [1, 12] implies positive and bounded",
    );
}

/// Test 5: Stator elastomer thickness scaled x10 (mm) must stay in valid range.
#[test]
fn test_progressing_cavity_pump_stator_thickness_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thick_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "thickness_range",
        "thick_x10 > 0 && thick_x10 < 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "thickness_positive_and_bounded",
        "thick_x10 >= 1 && thick_x10 <= 499",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stator thickness x10 in (0, 500) implies [1, 499]");
}

/// Test 6: Rotor eccentricity scaled x100 (mm) must stay in valid range.
#[test]
fn test_progressing_cavity_pump_rotor_eccentricity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ecc_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eccentricity_range",
        "ecc_x100 > 0 && ecc_x100 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eccentricity_positive_and_bounded",
        "ecc_x100 >= 1 && ecc_x100 <= 9999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotor eccentricity x100 in (0, 10000) implies [1, 9999]",
    );
}

/// Test 7: Stator material must be one of NBR(1), EPDM(2), or fluoroelastomer(3).
#[test]
fn test_progressing_cavity_pump_stator_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "material_valid",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "material_in_range",
        "mat >= 1 && mat <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "stator material disjunction (1=NBR, 2=EPDM, 3=fluoroelastomer) implies [1, 3]",
    );
}

/// Test 8: Drive coupling must be one of pin-joint(1), flex-rod(2), or gear-joint(3).
#[test]
fn test_progressing_cavity_pump_drive_coupling_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coupling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "coupling_valid",
        "coupling == 1 || coupling == 2 || coupling == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "coupling_in_range",
        "coupling >= 1 && coupling <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive coupling disjunction (1=pin-joint, 2=flex-rod, 3=gear-joint) implies [1, 3]",
    );
}

/// Test 9: Seal type must be one of mechanical(1), packed-gland(2), or lip-seal(3).
#[test]
fn test_progressing_cavity_pump_seal_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "seal_valid",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "seal_in_range",
        "seal >= 1 && seal <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seal type disjunction (1=mechanical, 2=packed-gland, 3=lip-seal) implies [1, 3]",
    );
}

/// Test 10: Run-dry protection flag (i32 boolean: 0 or 1) must be valid.
#[test]
fn test_progressing_cavity_pump_run_dry_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("run_dry_protect", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_boolean",
        "run_dry_protect == 0 || run_dry_protect == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded",
        "run_dry_protect >= 0 && run_dry_protect <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "run-dry protection flag (0 or 1) implies bounded in [0, 1]",
    );
}
