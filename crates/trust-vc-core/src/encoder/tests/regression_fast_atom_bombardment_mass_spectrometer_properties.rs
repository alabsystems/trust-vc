// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// ---------------------------------------------------------------------------
// Fast atom bombardment mass spectrometer – property-based regression tests
// ---------------------------------------------------------------------------

/// Mass range in amu — bounded range.
#[test]
fn test_fab_ms_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mr_a",
        "mass >= 1 && mass <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mr_c",
        "mass >= 1 && mass <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAB MS mass range bounded");
}

/// Beam energy in keV — bounded range.
#[test]
fn test_fab_ms_beam_energy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "be_a",
        "energy >= 2 && energy <= 30",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "be_c",
        "energy >= 2 && energy <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAB MS beam energy bounded");
}

/// Beam current at ×10 µA — bounded range.
#[test]
fn test_fab_ms_beam_current_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bc_a",
        "curr_x10 >= 1 && curr_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bc_c",
        "curr_x10 >= 1 && curr_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAB MS beam current x10 bounded");
}

/// Source temperature with offset +100 °C — bounded range.
#[test]
fn test_fab_ms_source_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "temp_off >= 80 && temp_off <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "temp_off >= 80 && temp_off <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAB MS source temperature offset bounded");
}

/// Accelerating voltage in kV — bounded range.
#[test]
fn test_fab_ms_accelerating_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "av_a",
        "voltage >= 1 && voltage <= 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "av_c",
        "voltage >= 1 && voltage <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAB MS accelerating voltage bounded");
}

/// Matrix flow at ×100 µL/min — bounded range.
#[test]
fn test_fab_ms_matrix_flow_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mf_a",
        "flow_x100 >= 1 && flow_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mf_c",
        "flow_x100 >= 1 && flow_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAB MS matrix flow x100 bounded");
}

/// Atom source — 3-way disjunction.
#[test]
fn test_fab_ms_atom_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "as_a",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "as_c",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAB MS atom source three-way disjunction");
}

/// Matrix type — 3-way disjunction.
#[test]
fn test_fab_ms_matrix_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("matrix", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mt_a",
        "matrix == 1 || matrix == 2 || matrix == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mt_c",
        "matrix == 1 || matrix == 2 || matrix == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAB MS matrix type three-way disjunction");
}

/// Analyzer — 3-way disjunction.
#[test]
fn test_fab_ms_analyzer_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "an_a",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "an_c",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAB MS analyzer three-way disjunction");
}

/// Automatic beam optimization — boolean flag.
#[test]
fn test_fab_ms_auto_beam_optimization_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bo_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("bo_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAB MS auto beam optimization flag");
}
