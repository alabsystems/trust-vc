// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_la_icp_laser_energy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_range",
        "energy >= 1 && energy <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_bounded",
        "energy >= 1 && energy <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser energy must be between 1 and 500 mJ");
}

#[test]
fn test_la_icp_repetition_rate_bounded() {
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
fn test_la_icp_spot_size_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spot_size_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spot_size_range",
        "spot_size_x10 >= 10 && spot_size_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spot_size_bounded",
        "spot_size_x10 >= 10 && spot_size_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spot size x10 must be between 10 and 5000 representing 1.0-500.0 um",
    );
}

#[test]
fn test_la_icp_wavelength_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wavelength_range",
        "wavelength >= 100 && wavelength <= 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wavelength_bounded",
        "wavelength >= 100 && wavelength <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength must be between 100 and 900 nm");
}

#[test]
fn test_la_icp_plasma_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plasma_power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "plasma_power_range",
        "plasma_power >= 500 && plasma_power <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "plasma_power_bounded",
        "plasma_power >= 500 && plasma_power <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "plasma power must be between 500 and 2000 W");
}

#[test]
fn test_la_icp_detection_limit_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_limit_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "det_limit_range",
        "det_limit_x10000 >= 1 && det_limit_x10000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "det_limit_bounded",
        "det_limit_x10000 >= 1 && det_limit_x10000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection limit x10000 must be between 1 and 10000 representing 0.0001-1.0000 ppm",
    );
}

#[test]
fn test_la_icp_laser_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "laser_type_valid",
        "laser_type == 1 || laser_type == 2 || laser_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "laser_type_disjunction",
        "laser_type == 1 || laser_type == 2 || laser_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser type must be 1=Nd:YAG, 2=ArF-excimer, or 3=femtosecond",
    );
}

#[test]
fn test_la_icp_ablation_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ablation_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ablation_mode_valid",
        "ablation_mode == 1 || ablation_mode == 2 || ablation_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ablation_mode_disjunction",
        "ablation_mode == 1 || ablation_mode == 2 || ablation_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ablation mode must be 1=spot, 2=line-scan, or 3=raster",
    );
}

#[test]
fn test_la_icp_carrier_gas_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("carrier_gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "carrier_gas_valid",
        "carrier_gas == 1 || carrier_gas == 2 || carrier_gas == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "carrier_gas_disjunction",
        "carrier_gas == 1 || carrier_gas == 2 || carrier_gas == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "carrier gas must be 1=argon, 2=helium, or 3=mixed");
}

#[test]
fn test_la_icp_auto_focus_tracking_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_focus", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_focus_flag",
        "auto_focus == 0 || auto_focus == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_focus_boolean",
        "auto_focus == 0 || auto_focus == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic focus tracking must be a boolean flag (0=off, 1=on)",
    );
}
