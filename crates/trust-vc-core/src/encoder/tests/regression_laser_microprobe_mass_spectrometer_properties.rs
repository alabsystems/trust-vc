// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_lmms_laser_energy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_range",
        "energy_x100 >= 1 && energy_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_bounded",
        "energy_x100 >= 1 && energy_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser energy x100 bounded 0.01 mJ resolution");
}

#[test]
fn test_lmms_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_range",
        "mass >= 1 && mass <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mass_bounded",
        "mass >= 1 && mass <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range bounded 1 to 100000 amu");
}

#[test]
fn test_lmms_spatial_resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res_x10 >= 1 && res_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_bounded",
        "res_x10 >= 1 && res_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spatial resolution x10 bounded 0.1 micrometer resolution",
    );
}

#[test]
fn test_lmms_mass_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolving", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolving_range",
        "resolving >= 100 && resolving <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolving_bounded",
        "resolving >= 100 && resolving <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass resolving power bounded 100 to 50000");
}

#[test]
fn test_lmms_repetition_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "rate >= 1 && rate <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rate_bounded",
        "rate >= 1 && rate <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repetition rate bounded 1 to 10000 Hz");
}

#[test]
fn test_lmms_laser_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "laser_type",
        "lt == 1 || lt == 2 || lt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "laser_type_valid",
        "lt == 1 || lt == 2 || lt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser type three-way 1=Nd-YAG 2=excimer 3=nitrogen",
    );
}

#[test]
fn test_lmms_ion_polarity_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pol", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "polarity",
        "pol == 1 || pol == 2 || pol == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "polarity_valid",
        "pol == 1 || pol == 2 || pol == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ion polarity three-way 1=positive 2=negative 3=dual",
    );
}

#[test]
fn test_lmms_analyzer_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("at", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "analyzer",
        "at == 1 || at == 2 || at == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "analyzer_valid",
        "at == 1 || at == 2 || at == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analyzer type three-way 1=TOF 2=magnetic-sector 3=quadrupole",
    );
}

#[test]
fn test_lmms_auto_focus_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_bool",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-focus flag boolean 0 or 1");
}

#[test]
fn test_lmms_spot_diameter_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spot_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spot_range",
        "spot_x10 >= 1 && spot_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spot_bounded",
        "spot_x10 >= 1 && spot_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spot diameter x10 bounded 0.1 micrometer resolution",
    );
}
