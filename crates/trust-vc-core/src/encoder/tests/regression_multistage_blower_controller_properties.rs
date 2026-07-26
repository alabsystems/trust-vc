// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_multistage_blower_airflow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 > 0 && flow_x10 < 500000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 > 0 && flow_x10 < 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "airflow x10 must be in range (0, 500000) representing 0.0-50000.0 m3/min",
    );
}

#[test]
fn test_multistage_blower_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 > 0 && press_x10 < 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press_x10 > 0 && press_x10 < 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 must be in range (0, 20000) representing 0.0-2000.0 kPa",
    );
}

#[test]
fn test_multistage_blower_impeller_diameter_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diam_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diam_range",
        "diam_x10 > 0 && diam_x10 < 30000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diam_bounded",
        "diam_x10 > 0 && diam_x10 < 30000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impeller diameter x10 must be in range (0, 30000) representing 0.0-3000.0 mm",
    );
}

#[test]
fn test_multistage_blower_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stages_range",
        "stages >= 2 && stages <= 12",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stages_bounded",
        "stages >= 2 && stages <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of stages must be between 2 and 12");
}

#[test]
fn test_multistage_blower_rotation_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 1000 && rpm <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_bounded",
        "rpm >= 1000 && rpm <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed must be between 1000 and 50000 RPM");
}

#[test]
fn test_multistage_blower_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pwr", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pwr_range",
        "pwr >= 1 && pwr <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pwr_bounded",
        "pwr >= 1 && pwr <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power must be between 1 and 5000 kW");
}

#[test]
fn test_multistage_blower_impeller_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("itype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "itype_range",
        "itype == 1 || itype == 2 || itype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "itype_valid",
        "itype == 1 || itype == 2 || itype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impeller type must be open (1), semi-open (2), or shrouded (3)",
    );
}

#[test]
fn test_multistage_blower_intercooler_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cool", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cool_range",
        "cool == 1 || cool == 2 || cool == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cool_valid",
        "cool == 1 || cool == 2 || cool == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "intercooler type must be air (1), water (2), or none (3)",
    );
}

#[test]
fn test_multistage_blower_sealing_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "seal_range",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "seal_valid",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sealing type must be labyrinth (1), dry-gas (2), or carbon-ring (3)",
    );
}

#[test]
fn test_multistage_blower_anti_surge_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("surge", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "surge_range",
        "surge == 0 || surge == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "surge_valid",
        "surge == 0 || surge == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic anti-surge control flag must be 0 (disabled) or 1 (enabled)",
    );
}
