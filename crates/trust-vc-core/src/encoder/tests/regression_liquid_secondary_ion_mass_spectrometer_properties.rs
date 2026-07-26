// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_liquid_sims_mass_range_amu() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_a",
        "mass >= 1 && mass <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mass_c",
        "mass >= 1 && mass <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "liquid SIMS mass range valid in 1-10000 amu");
}

#[test]
fn test_liquid_sims_primary_beam_energy_kev() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_a",
        "energy >= 1 && energy <= 30",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_c",
        "energy >= 1 && energy <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "liquid SIMS primary beam energy valid in 1-30 keV");
}

#[test]
fn test_liquid_sims_primary_beam_current_na() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curr_a",
        "curr_x10 >= 1 && curr_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "curr_c",
        "curr_x10 >= 1 && curr_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid SIMS primary beam current valid at x10 nA scale",
    );
}

#[test]
fn test_liquid_sims_extraction_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_a",
        "voltage >= 100 && voltage <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_c",
        "voltage >= 100 && voltage <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid SIMS extraction voltage valid in 100-10000 V",
    );
}

#[test]
fn test_liquid_sims_chamber_pressure() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_a",
        "press_x1000 >= 1 && press_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_c",
        "press_x1000 >= 1 && press_x1000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid SIMS chamber pressure valid at x1000 torr scale",
    );
}

#[test]
fn test_liquid_sims_liquid_flow_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_a",
        "flow_x100 >= 1 && flow_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_c",
        "flow_x100 >= 1 && flow_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid SIMS liquid flow rate valid at x100 uL/min scale",
    );
}

#[test]
fn test_liquid_sims_primary_ion_species() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ion", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ion_a", "ion >= 1 && ion <= 3"));
    ctx.push_obligation(ProofObligation::assert(
        "ion_c",
        "ion == 1 || ion == 2 || ion == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "liquid SIMS primary ion species is Ga, Bi, or Au");
}

#[test]
fn test_liquid_sims_analyzer_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "analyzer_a",
        "analyzer >= 1 && analyzer <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "analyzer_c",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid SIMS analyzer is TOF, magnetic-sector, or quadrupole",
    );
}

#[test]
fn test_liquid_sims_matrix_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("matrix", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "matrix_a",
        "matrix >= 1 && matrix <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "matrix_c",
        "matrix == 1 || matrix == 2 || matrix == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "liquid SIMS matrix is glycerol, diethanolamine, or triethanolamine",
    );
}

#[test]
fn test_liquid_sims_auto_beam_alignment() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("align", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "align_a",
        "align >= 0 && align <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "align_c",
        "align == 0 || align == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "liquid SIMS auto beam alignment is a boolean flag");
}
