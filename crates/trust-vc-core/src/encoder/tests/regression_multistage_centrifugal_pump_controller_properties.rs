// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_multistage_pump_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stages_range",
        "stages >= 2 && stages <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stages_bounded",
        "stages >= 2 && stages <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stage count must be between 2 and 20");
}

#[test]
fn test_multistage_pump_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow >= 10 && flow <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow >= 10 && flow <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate must be between 10 and 100000 L/min");
}

#[test]
fn test_multistage_pump_head_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "head_range",
        "head >= 50 && head <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "head_bounded",
        "head >= 50 && head <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "total head must be between 50 and 5000 meters");
}

#[test]
fn test_multistage_pump_efficiency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eff_range",
        "eff_x10 >= 500 && eff_x10 <= 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eff_bounded",
        "eff_x10 >= 500 && eff_x10 <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "efficiency x10 must be between 500 and 900 (50.0%-90.0%)",
    );
}

#[test]
fn test_multistage_pump_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 1000 && rpm <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_bounded",
        "rpm >= 1000 && rpm <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed must be between 1000 and 6000 RPM");
}

#[test]
fn test_multistage_pump_power_bounded() {
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
fn test_multistage_pump_casing_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cas", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cas_range",
        "cas == 1 || cas == 2 || cas == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cas_valid",
        "cas == 1 || cas == 2 || cas == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "casing type must be ring section (1), barrel (2), or axially split (3)",
    );
}

#[test]
fn test_multistage_pump_impeller_trim_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trim", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "trim_range",
        "trim == 1 || trim == 2 || trim == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "trim_valid",
        "trim == 1 || trim == 2 || trim == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impeller trim must be full (1), reduced (2), or minimum (3)",
    );
}

#[test]
fn test_multistage_pump_seal_type_three_way() {
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
        "seal type must be mechanical (1), packing (2), or magnetic (3)",
    );
}

#[test]
fn test_multistage_pump_balance_drum_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bal", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bal_range", "bal == 0 || bal == 1"));
    ctx.push_obligation(ProofObligation::assert("bal_valid", "bal == 0 || bal == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "balance drum flag must be 0 (absent) or 1 (present)",
    );
}
