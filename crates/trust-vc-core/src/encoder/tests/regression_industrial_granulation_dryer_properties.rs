// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_granulation_dryer_batch_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batch", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "batch_range",
        "batch >= 5 && batch <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "batch_bounded",
        "batch >= 5 && batch <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "batch size must be between 5 and 5000 kg");
}

#[test]
fn test_granulation_dryer_spray_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spray_range",
        "spray_x10 >= 1 && spray_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spray_bounded",
        "spray_x10 >= 1 && spray_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spray rate x10 must be in range 1-10000 representing 0.1-1000.0 mL/min",
    );
}

#[test]
fn test_granulation_dryer_inlet_air_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 130 && temp_off <= 480",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_off >= 130 && temp_off <= 480",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inlet air temperature offset+100 must be in range 130-480 representing 30-380 C",
    );
}

#[test]
fn test_granulation_dryer_fluidization_velocity_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vel_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vel_range",
        "vel_x10 >= 5 && vel_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vel_bounded",
        "vel_x10 >= 5 && vel_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fluidization velocity x10 must be in range 5-200 representing 0.5-20.0 m/s",
    );
}

#[test]
fn test_granulation_dryer_product_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prod_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "prod_range",
        "prod_off >= 110 && prod_off <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "prod_bounded",
        "prod_off >= 110 && prod_off <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "product temperature offset+100 must be in range 110-300 representing 10-200 C",
    );
}

#[test]
fn test_granulation_dryer_spray_nozzles_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nozzles", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nozzles_range",
        "nozzles >= 1 && nozzles <= 24",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nozzles_bounded",
        "nozzles >= 1 && nozzles <= 24",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of spray nozzles must be between 1 and 24");
}

#[test]
fn test_granulation_dryer_spray_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stype_range",
        "stype == 1 || stype == 2 || stype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stype_valid",
        "stype == 1 || stype == 2 || stype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spray type must be top-spray (1), bottom-spray (2), or tangential-spray (3)",
    );
}

#[test]
fn test_granulation_dryer_binder_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("binder", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "binder_range",
        "binder == 1 || binder == 2 || binder == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "binder_valid",
        "binder == 1 || binder == 2 || binder == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "binder type must be aqueous (1), organic-solvent (2), or melt (3)",
    );
}

#[test]
fn test_granulation_dryer_filter_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("filt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "filt_range",
        "filt == 1 || filt == 2 || filt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "filt_valid",
        "filt == 1 || filt == 2 || filt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "filter type must be bag (1), cartridge (2), or shaker (3)",
    );
}

#[test]
fn test_granulation_dryer_auto_endpoint_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("endpt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "endpt_range",
        "endpt == 0 || endpt == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "endpt_valid",
        "endpt == 0 || endpt == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic endpoint detection flag must be 0 (disabled) or 1 (enabled)",
    );
}
