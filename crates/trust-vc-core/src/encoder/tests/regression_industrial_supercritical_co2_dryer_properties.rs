// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_sc_co2_pressure_bar_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pr_a",
        "pressure_bar >= 74 && pressure_bar <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pr_c",
        "pressure_bar >= 74 && pressure_bar <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pressure in [74, 600] bar (above CO2 critical point 73.8 bar)",
    );
}

#[test]
fn test_sc_co2_temperature_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tp_a",
        "temp_x10 >= 310 && temp_x10 <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tp_c",
        "temp_x10 >= 310 && temp_x10 <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temperature x10 in [310, 1500] representing 31.0-150.0 C (above critical 31.1 C)",
    );
}

#[test]
fn test_sc_co2_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("co2_flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cf_a",
        "co2_flow >= 1 && co2_flow <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cf_c",
        "co2_flow >= 1 && co2_flow <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CO2 flow rate in [1, 10000] g/min");
}

#[test]
fn test_sc_co2_vessel_volume_ml_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vessel_ml", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vv_a",
        "vessel_ml >= 10 && vessel_ml <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vv_c",
        "vessel_ml >= 10 && vessel_ml <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vessel volume in [10, 100000] mL (10mL-100L)");
}

#[test]
fn test_sc_co2_depressurization_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depress_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dr_a",
        "depress_x10 >= 1 && depress_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dr_c",
        "depress_x10 >= 1 && depress_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "depressurization rate x10 in [1, 500] representing 0.1-50.0 bar/min",
    );
}

#[test]
fn test_sc_co2_cosolvent_fraction_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cosolv_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cs_a",
        "cosolv_x100 >= 0 && cosolv_x100 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cs_c",
        "cosolv_x100 >= 0 && cosolv_x100 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cosolvent fraction x100 in [0, 2000] representing 0.00-20.00%",
    );
}

#[test]
fn test_sc_co2_application_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("application", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ap_a",
        "application == 1 || application == 2 || application == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ap_c",
        "application == 1 || application == 2 || application == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "application: aerogel drying, food dehydration, or pharmaceutical processing",
    );
}

#[test]
fn test_sc_co2_cosolvent_type_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cosolvent", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ct_a",
        "cosolvent == 1 || cosolvent == 2 || cosolvent == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ct_c",
        "cosolvent == 1 || cosolvent == 2 || cosolvent == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cosolvent: ethanol, methanol, or acetone");
}

#[test]
fn test_sc_co2_separator_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("separator", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sp_a",
        "separator == 1 || separator == 2 || separator == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sp_c",
        "separator == 1 || separator == 2 || separator == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "separator: cyclone, gravity, or membrane");
}

#[test]
fn test_sc_co2_recycling_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("recycle", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rc_a",
        "recycle == 0 || recycle == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rc_c",
        "recycle == 0 || recycle == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CO2 recycling flag is boolean");
}
