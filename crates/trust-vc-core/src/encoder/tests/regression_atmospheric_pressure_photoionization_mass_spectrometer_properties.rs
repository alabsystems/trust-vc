// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_appi_ms_lamp_energy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "le_a",
        "energy_x100 >= 800 && energy_x100 <= 1300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "le_c",
        "energy_x100 >= 800 && energy_x100 <= 1300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "APPI-MS lamp energy x100 bounded");
}

#[test]
fn test_appi_ms_vaporizer_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vap_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vt_a",
        "vap_temp >= 200 && vap_temp <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vt_c",
        "vap_temp >= 200 && vap_temp <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "APPI-MS vaporizer temperature offset+100 bounded");
}

#[test]
fn test_appi_ms_nebulizer_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("neb_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nf_a",
        "neb_x10 >= 1 && neb_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nf_c",
        "neb_x10 >= 1 && neb_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "APPI-MS nebulizer flow x10 bounded");
}

#[test]
fn test_appi_ms_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mr_a",
        "mass >= 50 && mass <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mr_c",
        "mass >= 50 && mass <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "APPI-MS mass range bounded");
}

#[test]
fn test_appi_ms_dopant_flow_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dopant_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "df_a",
        "dopant_x100 >= 1 && dopant_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "df_c",
        "dopant_x100 >= 1 && dopant_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "APPI-MS dopant flow x100 bounded");
}

#[test]
fn test_appi_ms_corona_current_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("corona_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cc_a",
        "corona_x10 >= 1 && corona_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cc_c",
        "corona_x10 >= 1 && corona_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "APPI-MS corona current x10 bounded");
}

#[test]
fn test_appi_ms_lamp_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lamp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ls_a",
        "lamp == 1 || lamp == 2 || lamp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ls_c",
        "lamp == 1 || lamp == 2 || lamp == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "APPI-MS lamp source three-way disjunction");
}

#[test]
fn test_appi_ms_ionization_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ion_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "im_a",
        "ion_mode == 1 || ion_mode == 2 || ion_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "im_c",
        "ion_mode == 1 || ion_mode == 2 || ion_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "APPI-MS ionization mode three-way disjunction");
}

#[test]
fn test_appi_ms_polarity_three_way() {
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
    expect_verified(&result, "APPI-MS polarity three-way disjunction");
}

#[test]
fn test_appi_ms_auto_lamp_ignition_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("li_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("li_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "APPI-MS auto lamp ignition flag");
}
