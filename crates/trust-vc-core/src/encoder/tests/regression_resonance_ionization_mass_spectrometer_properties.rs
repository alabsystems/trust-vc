// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_rims_laser_wavelength_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_wavelength",
        "wavelength >= 200 && wavelength <= 1100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_wavelength",
        "wavelength >= 200 && wavelength <= 1100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser wavelength bounded 200-1100 nm");
}

#[test]
fn test_rims_ionization_efficiency_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_eff",
        "eff_x100 >= 1 && eff_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_eff",
        "eff_x100 >= 1 && eff_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ionization efficiency x100 bounded 0.01-100%");
}

#[test]
fn test_rims_mass_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolving", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_resolving",
        "resolving >= 100 && resolving <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_resolving",
        "resolving >= 100 && resolving <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass resolution bounded 100-100000");
}

#[test]
fn test_rims_repetition_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_rate",
        "rate >= 1 && rate <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_rate",
        "rate >= 1 && rate <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repetition rate bounded 1-50000 Hz");
}

#[test]
fn test_rims_sample_temperature_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_temp",
        "temp_off >= 200 && temp_off <= 3500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_temp",
        "temp_off >= 200 && temp_off <= 3500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample temperature offset+500 bounded representing -300 to 3000 K",
    );
}

#[test]
fn test_rims_laser_scheme_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scheme", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_scheme",
        "scheme == 1 || scheme == 2 || scheme == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_scheme",
        "scheme == 1 || scheme == 2 || scheme == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser scheme three-way: two-step, three-step, or autoionization",
    );
}

#[test]
fn test_rims_atomization_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_method",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_method",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "atomization method three-way: graphite-furnace, laser-ablation, or thermal-evaporation",
    );
}

#[test]
fn test_rims_mass_analyzer_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ma", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_ma",
        "ma == 1 || ma == 2 || ma == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_ma",
        "ma == 1 || ma == 2 || ma == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mass analyzer three-way: TOF, magnetic-sector, or quadrupole",
    );
}

#[test]
fn test_rims_auto_wavelength_tuning_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_flag",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_flag",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto wavelength tuning flag is boolean");
}

#[test]
fn test_rims_pulse_energy_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_energy",
        "energy_x1000 >= 1 && energy_x1000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_energy",
        "energy_x1000 >= 1 && energy_x1000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulse energy x1000 bounded 0.001-100 mJ");
}
