// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_appi_photon_energy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("photon_e_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pe_a",
        "photon_e_x100 >= 700 && photon_e_x100 <= 1300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pe_c",
        "photon_e_x100 >= 700 && photon_e_x100 <= 1300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "photon energy x100 in [700, 1300]");
}

#[test]
fn test_appi_vaporizer_temp_bounded() {
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
    expect_verified(&result, "vaporizer temperature in [200, 600] C");
}

#[test]
fn test_appi_nebulizer_gas_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("neb_flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nf_a",
        "neb_flow_x10 >= 5 && neb_flow_x10 <= 80",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nf_c",
        "neb_flow_x10 >= 5 && neb_flow_x10 <= 80",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nebulizer gas flow x10 in [5, 80]");
}

#[test]
fn test_appi_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mr_a",
        "mz_range >= 10 && mz_range <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mr_c",
        "mz_range >= 10 && mz_range <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range in [10, 4000] m/z");
}

#[test]
fn test_appi_liquid_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("liq_flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lf_a",
        "liq_flow_x10 >= 1 && liq_flow_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lf_c",
        "liq_flow_x10 >= 1 && liq_flow_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "liquid flow x10 in [1, 200]");
}

#[test]
fn test_appi_dopant_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dop_flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "df_a",
        "dop_flow_x10 >= 0 && dop_flow_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "df_c",
        "dop_flow_x10 >= 0 && dop_flow_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dopant flow x10 in [0, 200]");
}

#[test]
fn test_appi_lamp_type_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lamp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lt_a",
        "lamp == 1 || lamp == 2 || lamp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lt_c",
        "lamp == 1 || lamp == 2 || lamp == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lamp type: krypton, xenon, or argon");
}

#[test]
fn test_appi_dopant_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dopant", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "dopant == 1 || dopant == 2 || dopant == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "dopant == 1 || dopant == 2 || dopant == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dopant: toluene, anisole, or chlorobenzene");
}

#[test]
fn test_appi_mechanism_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mechanism", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mc_a",
        "mechanism == 1 || mechanism == 2 || mechanism == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mc_c",
        "mechanism == 1 || mechanism == 2 || mechanism == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mechanism: direct photoionization, charge exchange, or proton transfer",
    );
}

#[test]
fn test_appi_heated_nebulizer_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heated_neb", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hn_a",
        "heated_neb == 0 || heated_neb == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hn_c",
        "heated_neb == 0 || heated_neb == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heated nebulizer flag is boolean");
}
