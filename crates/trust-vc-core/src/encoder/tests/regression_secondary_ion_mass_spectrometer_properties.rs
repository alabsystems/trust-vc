// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_sims_mass_range_amu_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mass_val", "mass == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "mass_bounded",
        "mass >= 1 && mass <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range 250 amu in [1, 500]");
}

#[test]
fn test_sims_mass_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_val",
        "resolution == 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_bounded",
        "resolution >= 300 && resolution <= 30000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass resolution m/dm 5000 in [300, 30000]");
}

#[test]
fn test_sims_lateral_resolution_x10_nm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lateral_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lateral_x10_val",
        "lateral_x10 == 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lateral_x10_bounded",
        "lateral_x10 >= 500 && lateral_x10 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lateral resolution 500.0 nm (x10=5000) in [500, 100000]",
    );
}

#[test]
fn test_sims_depth_resolution_x10_nm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("depth_x10_val", "depth_x10 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "depth_x10_bounded",
        "depth_x10 >= 5 && depth_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "depth resolution 1.0 nm (x10=10) in [5, 100]");
}

#[test]
fn test_sims_detection_limit_ppb_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("limit_val", "limit == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "limit_bounded",
        "limit >= 1 && limit <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection limit 10 ppb in [1, 1000]");
}

#[test]
fn test_sims_primary_ion_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume("source_val", "source == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "source_valid",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "primary ion source 1=Cs+ in {1=Cs+, 2=O2+, 3=Ga+}");
}

#[test]
fn test_sims_analysis_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analysis mode 2=dynamic in {1=static, 2=dynamic, 3=imaging}",
    );
}

#[test]
fn test_sims_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume("detector_val", "detector == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "detector_valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector type 3=microchannel-plate in {1=electron-multiplier, 2=faraday-cup, 3=microchannel-plate}");
}

#[test]
fn test_sims_sputter_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rate_x100_val", "rate_x100 == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "rate_x100_bounded",
        "rate_x100 >= 10 && rate_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sputter rate 5.00 nm/s (x100=500) in [10, 10000]");
}

#[test]
fn test_sims_charge_compensation_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "charge_compensation_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "charge compensation flag=1 yields active (1)");
}
