// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_sesi_spray_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_v", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sv_a",
        "spray_v >= 500 && spray_v <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sv_c",
        "spray_v >= 500 && spray_v <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spray voltage in [500, 5000] V");
}

#[test]
fn test_sesi_solvent_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sf_a",
        "flow_x10 >= 1 && flow_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sf_c",
        "flow_x10 >= 1 && flow_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solvent flow x10 in [1, 500] representing 0.1-50.0 uL/min",
    );
}

#[test]
fn test_sesi_ion_source_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("src_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "it_a",
        "src_temp >= 50 && src_temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "it_c",
        "src_temp >= 50 && src_temp <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ion source temperature in [50, 500] C");
}

#[test]
fn test_sesi_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mr_a",
        "mz_max >= 50 && mz_max <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mr_c",
        "mz_max >= 50 && mz_max <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range in [50, 3000] m/z");
}

#[test]
fn test_sesi_drying_gas_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gf_a",
        "gas_flow >= 1 && gas_flow <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gf_c",
        "gas_flow >= 1 && gas_flow <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drying gas flow in [1, 20] L/min");
}

#[test]
fn test_sesi_capillary_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_v", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cv_a",
        "cap_v >= 100 && cap_v <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cv_c",
        "cap_v >= 100 && cap_v <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "capillary voltage in [100, 4000] V");
}

#[test]
fn test_sesi_solvent_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("solvent", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sl_a",
        "solvent == 1 || solvent == 2 || solvent == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sl_c",
        "solvent == 1 || solvent == 2 || solvent == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solvent: methanol-water, acetonitrile-water, or formic acid",
    );
}

#[test]
fn test_sesi_sample_introduction_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("intro_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "si_a",
        "intro_mode == 1 || intro_mode == 2 || intro_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "si_c",
        "intro_mode == 1 || intro_mode == 2 || intro_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample intro: direct headspace, breath sampling, or skin emission",
    );
}

#[test]
fn test_sesi_polarity_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polarity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "po_a",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "po_c",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "polarity: positive, negative, or alternating");
}

#[test]
fn test_sesi_real_time_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("real_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rt_a",
        "real_time == 0 || real_time == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rt_c",
        "real_time == 0 || real_time == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "real-time monitoring flag is boolean");
}
