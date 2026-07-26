// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_snms_sputter_energy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy", i32_ty());
    ctx.push_obligation(ProofObligation::assume("snms_energy_lo", "energy >= 100"));
    ctx.push_obligation(ProofObligation::assume("snms_energy_hi", "energy <= 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "snms_energy_bounded",
        "energy >= 100 && energy <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sputter energy bounded 100-10000 eV");
}

#[test]
fn test_snms_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume("snms_mass_lo", "mass >= 1"));
    ctx.push_obligation(ProofObligation::assume("snms_mass_hi", "mass <= 500"));
    ctx.push_obligation(ProofObligation::assert(
        "snms_mass_bounded",
        "mass >= 1 && mass <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range bounded 1-500 amu");
}

#[test]
fn test_snms_depth_resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("snms_res_lo", "res_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assume("snms_res_hi", "res_x10 <= 100"));
    ctx.push_obligation(ProofObligation::assert(
        "snms_res_bounded",
        "res_x10 >= 1 && res_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "depth resolution x10 bounded 1-100 in 0.1 nm");
}

#[test]
fn test_snms_ionization_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume("snms_rate_lo", "rate_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assume(
        "snms_rate_hi",
        "rate_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "snms_rate_bounded",
        "rate_x100 >= 1 && rate_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionization rate x100 bounded 1-10000 in 0.01 percent",
    );
}

#[test]
fn test_snms_sputter_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sput_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume("snms_sput_lo", "sput_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assume(
        "snms_sput_hi",
        "sput_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "snms_sput_bounded",
        "sput_x100 >= 1 && sput_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sputter rate x100 bounded 1-50000 in 0.01 nm/s");
}

#[test]
fn test_snms_ionization_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("src", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "snms_src_valid",
        "src == 1 || src == 2 || src == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "snms_src_three_way",
        "src == 1 || src == 2 || src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionization source three-way: 1=electron-gas, 2=laser, 3=plasma",
    );
}

#[test]
fn test_snms_sputter_ion_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("si", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "snms_si_valid",
        "si == 1 || si == 2 || si == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "snms_si_three_way",
        "si == 1 || si == 2 || si == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sputter ion three-way: 1=argon, 2=cesium, 3=oxygen",
    );
}

#[test]
fn test_snms_analyzer_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("at", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "snms_at_valid",
        "at == 1 || at == 2 || at == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "snms_at_three_way",
        "at == 1 || at == 2 || at == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analyzer type three-way: 1=quadrupole, 2=TOF, 3=magnetic-sector",
    );
}

#[test]
fn test_snms_auto_crater_profiling_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "snms_flag_valid",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "snms_flag_boolean",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto crater profiling flag is boolean");
}

#[test]
fn test_snms_detection_limit_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("limit_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume("snms_limit_lo", "limit_x1000 >= 1"));
    ctx.push_obligation(ProofObligation::assume(
        "snms_limit_hi",
        "limit_x1000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "snms_limit_bounded",
        "limit_x1000 >= 1 && limit_x1000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection limit x1000 bounded 1-100000 in 0.001 ppm",
    );
}
