// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_vacuum_arc_chamber_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cp_a",
        "press_x10 >= 1 && press_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cp_c",
        "press_x10 >= 1 && press_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum arc chamber pressure x10 bounded");
}

#[test]
fn test_vacuum_arc_arc_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("arc_curr", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ac_a",
        "arc_curr >= 10 && arc_curr <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ac_c",
        "arc_curr >= 10 && arc_curr <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum arc current bounded");
}

#[test]
fn test_vacuum_arc_cathode_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cath_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ct_a",
        "cath_temp >= 200 && cath_temp <= 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ct_c",
        "cath_temp >= 200 && cath_temp <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum arc cathode temperature offset+100 bounded");
}

#[test]
fn test_vacuum_arc_deposition_rate_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dr_a",
        "rate_x1000 >= 1 && rate_x1000 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dr_c",
        "rate_x1000 >= 1 && rate_x1000 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum arc deposition rate x1000 bounded");
}

#[test]
fn test_vacuum_arc_substrate_bias_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bias", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sb_a", "bias >= 0 && bias <= 1200"));
    ctx.push_obligation(ProofObligation::assert("sb_c", "bias >= 0 && bias <= 1200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum arc substrate bias bounded");
}

#[test]
fn test_vacuum_arc_pulse_duration_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pulse_us", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pd_a",
        "pulse_us >= 1 && pulse_us <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pd_c",
        "pulse_us >= 1 && pulse_us <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum arc pulse duration bounded");
}

#[test]
fn test_vacuum_arc_cathode_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cm_a",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cm_c",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum arc cathode material three-way disjunction");
}

#[test]
fn test_vacuum_arc_discharge_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dm_a",
        "discharge == 1 || discharge == 2 || discharge == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dm_c",
        "discharge == 1 || discharge == 2 || discharge == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum arc discharge mode three-way disjunction");
}

#[test]
fn test_vacuum_arc_gas_injection_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gi_a",
        "gas == 1 || gas == 2 || gas == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gi_c",
        "gas == 1 || gas == 2 || gas == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum arc gas injection three-way disjunction");
}

#[test]
fn test_vacuum_arc_auto_arc_stabilization_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("as_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("as_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum arc auto arc stabilization flag");
}
