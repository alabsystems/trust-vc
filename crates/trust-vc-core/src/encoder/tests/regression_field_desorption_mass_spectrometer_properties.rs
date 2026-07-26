// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_fd_ms_emitter_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ec_a",
        "curr_x100 >= 1 && curr_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ec_c",
        "curr_x100 >= 1 && curr_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FD-MS emitter current x100 bounded");
}

#[test]
fn test_fd_ms_emitter_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ev_a",
        "voltage >= 1 && voltage <= 15000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ev_c",
        "voltage >= 1 && voltage <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FD-MS emitter voltage bounded");
}

#[test]
fn test_fd_ms_source_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("src_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "src_temp >= 120 && src_temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "src_temp >= 120 && src_temp <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FD-MS ion source temperature offset+100 bounded");
}

#[test]
fn test_fd_ms_mass_range_bounded() {
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
    expect_verified(&result, "FD-MS mass range bounded");
}

#[test]
fn test_fd_ms_counter_electrode_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ce_volt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cv_a",
        "ce_volt >= 0 && ce_volt <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cv_c",
        "ce_volt >= 0 && ce_volt <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FD-MS counter electrode voltage bounded");
}

#[test]
fn test_fd_ms_heating_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hr_a",
        "rate_x10 >= 1 && rate_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hr_c",
        "rate_x10 >= 1 && rate_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FD-MS heating rate x10 bounded");
}

#[test]
fn test_fd_ms_emitter_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "em_a",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "em_c",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FD-MS emitter material three-way disjunction");
}

#[test]
fn test_fd_ms_analyzer_three_way() {
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
    expect_verified(&result, "FD-MS analyzer three-way disjunction");
}

#[test]
fn test_fd_ms_sample_introduction_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("intro", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "si_a",
        "intro == 1 || intro == 2 || intro == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "si_c",
        "intro == 1 || intro == 2 || intro == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FD-MS sample introduction three-way disjunction");
}

#[test]
fn test_fd_ms_auto_emitter_conditioning_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ec_a2", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("ec_c2", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FD-MS auto emitter conditioning flag");
}
