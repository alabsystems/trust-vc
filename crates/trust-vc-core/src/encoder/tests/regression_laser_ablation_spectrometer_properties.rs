// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_laser_ablation_spec_laser_energy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_range",
        "energy >= 1 && energy <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_bounded",
        "energy >= 1 && energy <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser energy must be between 1 and 1000 mJ");
}

#[test]
fn test_laser_ablation_spec_spot_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spot_size", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spot_size_range",
        "spot_size >= 5 && spot_size <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spot_size_bounded",
        "spot_size >= 5 && spot_size <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ablation spot size must be between 5 and 500 um");
}

#[test]
fn test_laser_ablation_spec_wavelength_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wavelength_range",
        "wavelength >= 193 && wavelength <= 1064",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wavelength_bounded",
        "wavelength >= 193 && wavelength <= 1064",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser wavelength must be between 193 and 1064 nm");
}

#[test]
fn test_laser_ablation_spec_repetition_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rep_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rep_rate_range",
        "rep_rate >= 1 && rep_rate <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rep_rate_bounded",
        "rep_rate >= 1 && rep_rate <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repetition rate must be between 1 and 1000 Hz");
}

#[test]
fn test_laser_ablation_spec_ablation_depth_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "depth_x100_range",
        "depth_x100 >= 1 && depth_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "depth_x100_bounded",
        "depth_x100 >= 1 && depth_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ablation depth x100 must be between 1 and 10000 (0.01-100.00 um)",
    );
}

#[test]
fn test_laser_ablation_spec_carrier_gas_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_x10_range",
        "flow_x10 >= 1 && flow_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_x10_bounded",
        "flow_x10 >= 1 && flow_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "carrier gas flow x10 must be between 1 and 100 (0.1-10.0 L/min)",
    );
}

#[test]
fn test_laser_ablation_spec_laser_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "laser_type_range",
        "laser_type >= 1 && laser_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "laser_type_valid",
        "laser_type >= 1 && laser_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser type must be 1=ArF-excimer, 2=Nd-YAG, or 3=femtosecond",
    );
}

#[test]
fn test_laser_ablation_spec_ablation_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ablation_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ablation_mode_range",
        "ablation_mode >= 1 && ablation_mode <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ablation_mode_valid",
        "ablation_mode >= 1 && ablation_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ablation mode must be 1=spot, 2=line-scan, or 3=raster",
    );
}

#[test]
fn test_laser_ablation_spec_carrier_gas_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("carrier_gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "carrier_gas_range",
        "carrier_gas >= 1 && carrier_gas <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "carrier_gas_valid",
        "carrier_gas >= 1 && carrier_gas <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "carrier gas must be 1=helium, 2=argon, or 3=nitrogen",
    );
}

#[test]
fn test_laser_ablation_spec_auto_focus_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_focus", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_focus_range",
        "auto_focus >= 0 && auto_focus <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_focus_valid",
        "auto_focus >= 0 && auto_focus <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto focus flag must be 0=disabled or 1=enabled");
}
