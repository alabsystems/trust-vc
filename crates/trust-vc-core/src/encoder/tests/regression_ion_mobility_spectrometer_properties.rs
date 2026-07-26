// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_ims_detection_limit_ppb_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("limit_val", "limit == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "limit_bounded",
        "limit >= 1 && limit <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection limit 1 ppb in [1, 100]");
}

#[test]
fn test_ims_drift_tube_length_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", i32_ty());
    ctx.push_obligation(ProofObligation::assume("length_val", "length == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "length_bounded",
        "length >= 30 && length <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drift tube length 100 mm in [30, 300]");
}

#[test]
fn test_ims_response_time_s_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("response", i32_ty());
    ctx.push_obligation(ProofObligation::assume("response_val", "response == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "response_bounded",
        "response >= 1 && response <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time 5 s in [1, 30]");
}

#[test]
fn test_ims_ionization_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume("source_val", "source == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "source_valid",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionization source 1=Ni-63 in {1=Ni-63, 2=corona discharge, 3=photoionization}",
    );
}

#[test]
fn test_ims_polarity_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polarity", i32_ty());
    ctx.push_obligation(ProofObligation::assume("polarity_val", "polarity == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "polarity_valid",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "polarity 1=positive in {1=positive, 2=negative, 3=dual}",
    );
}

#[test]
fn test_ims_resolving_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume("power_val", "power == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power >= 20 && power <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolving power 60 in [20, 200]");
}

#[test]
fn test_ims_drift_gas_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume("gas_val", "gas == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "gas_valid",
        "gas == 1 || gas == 2 || gas == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drift gas 1=air in {1=air, 2=nitrogen, 3=helium}");
}

#[test]
fn test_ims_sample_flow_ml_per_min_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow >= 50 && flow <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample flow 500 mL/min in [50, 2000]");
}

#[test]
fn test_ims_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 550"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 500 && temp <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 50C (offset+500=550) in [500, 600]");
}

#[test]
fn test_ims_dopant_chemistry_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "dopant_chemistry_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dopant chemistry flag=1 yields active (1)");
}
