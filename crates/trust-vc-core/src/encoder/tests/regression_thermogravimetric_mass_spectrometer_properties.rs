// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_tga_ms_furnace_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("furnace_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ft_a",
        "furnace_temp >= 20 && furnace_temp <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ft_c",
        "furnace_temp >= 20 && furnace_temp <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA-MS furnace temperature bounded");
}

#[test]
fn test_tga_ms_heating_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hr_a",
        "rate_x10 >= 1 && rate_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hr_c",
        "rate_x10 >= 1 && rate_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA-MS heating rate x10 bounded");
}

#[test]
fn test_tga_ms_sample_mass_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sm_a",
        "mass_x1000 >= 1 && mass_x1000 <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sm_c",
        "mass_x1000 >= 1 && mass_x1000 <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA-MS sample mass x1000 bounded");
}

#[test]
fn test_tga_ms_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mr_a", "mz >= 1 && mz <= 300"));
    ctx.push_obligation(ProofObligation::assert("mr_c", "mz >= 1 && mz <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA-MS mass range bounded");
}

#[test]
fn test_tga_ms_balance_sensitivity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bs_a",
        "sens_x100 >= 1 && sens_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bs_c",
        "sens_x100 >= 1 && sens_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA-MS balance sensitivity x100 bounded");
}

#[test]
fn test_tga_ms_gas_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gf_a",
        "flow_x10 >= 1 && flow_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gf_c",
        "flow_x10 >= 1 && flow_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA-MS gas flow x10 bounded");
}

#[test]
fn test_tga_ms_atmosphere_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atmos", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_a",
        "atmos == 1 || atmos == 2 || atmos == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_c",
        "atmos == 1 || atmos == 2 || atmos == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA-MS atmosphere three-way disjunction");
}

#[test]
fn test_tga_ms_crucible_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("crucible", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cr_a",
        "crucible == 1 || crucible == 2 || crucible == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cr_c",
        "crucible == 1 || crucible == 2 || crucible == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA-MS crucible material three-way disjunction");
}

#[test]
fn test_tga_ms_ionization_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ionization", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "im_a",
        "ionization == 1 || ionization == 2 || ionization == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "im_c",
        "ionization == 1 || ionization == 2 || ionization == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA-MS ionization method three-way disjunction");
}

#[test]
fn test_tga_ms_auto_baseline_correction_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bc_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("bc_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TGA-MS auto baseline correction flag");
}
