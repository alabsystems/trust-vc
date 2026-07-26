// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_tma_temp_range_max_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_t", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "max_t_range",
        "max_t >= 520 && max_t <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "max_t_bounded",
        "max_t >= 520 && max_t <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max temp offset +500 bounded in [520, 2000]");
}

#[test]
fn test_tma_temp_range_min_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("min_t", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "min_t_range",
        "min_t >= 350 && min_t <= 525",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "min_t_bounded",
        "min_t >= 350 && min_t <= 525",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min temp offset +500 bounded in [350, 525]");
}

#[test]
fn test_tma_force_range_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("force_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "force_range",
        "force_x1000 >= 1 && force_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "force_bounded",
        "force_x1000 >= 1 && force_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "force x1000 bounded in [1, 10000]");
}

#[test]
fn test_tma_displacement_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disp_range",
        "disp_x1000 >= 1 && disp_x1000 <= 5000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disp_bounded",
        "disp_x1000 >= 1 && disp_x1000 <= 5000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement x1000 bounded in [1, 5000000]");
}

#[test]
fn test_tma_heating_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hr_range",
        "hr_x10 >= 1 && hr_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hr_bounded",
        "hr_x10 >= 1 && hr_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heating rate x10 bounded in [1, 2000]");
}

#[test]
fn test_tma_sample_length_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("len_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "len_range",
        "len_x10 >= 10 && len_x10 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "len_bounded",
        "len_x10 >= 10 && len_x10 <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample length x10 bounded in [10, 300]");
}

#[test]
fn test_tma_probe_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "probe_range",
        "probe == 1 || probe == 2 || probe == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "probe_valid",
        "probe == 1 || probe == 2 || probe == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "probe type is expansion, penetration, or tension");
}

#[test]
fn test_tma_atmosphere_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "atm_range",
        "atm == 1 || atm == 2 || atm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "atm_valid",
        "atm == 1 || atm == 2 || atm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "atmosphere is nitrogen, air, or helium");
}

#[test]
fn test_tma_cooling_method_three_way() {
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
        "cooling is mechanical, liquid nitrogen, or compressed air",
    );
}

#[test]
fn test_tma_modulated_mode_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mod_tma", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mod_range",
        "mod_tma == 0 || mod_tma == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mod_valid",
        "mod_tma == 0 || mod_tma == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "modulated TMA flag is boolean 0 or 1");
}
