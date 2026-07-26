// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_nanoesi_spray_voltage_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sv_a",
        "spray_x100 >= 5 && spray_x100 <= 250",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sv_c",
        "spray_x100 >= 5 && spray_x100 <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nanoESI spray voltage x100 in [5, 250] representing 0.05-2.50 kV",
    );
}

#[test]
fn test_nanoesi_flow_rate_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fr_a",
        "flow_x1000 >= 1 && flow_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fr_c",
        "flow_x1000 >= 1 && flow_x1000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate x1000 in [1, 1000] representing 0.001-1.000 uL/min",
    );
}

#[test]
fn test_nanoesi_emitter_tip_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tip_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "et_a",
        "tip_x10 >= 1 && tip_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "et_c",
        "tip_x10 >= 1 && tip_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "emitter tip x10 in [1, 500] representing 0.1-50.0 um ID",
    );
}

#[test]
fn test_nanoesi_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mz_a", "mz >= 50 && mz <= 8000"));
    ctx.push_obligation(ProofObligation::assert("mz_c", "mz >= 50 && mz <= 8000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nanoESI mass range in [50, 8000] m/z");
}

#[test]
fn test_nanoesi_capillary_inlet_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ct_a",
        "cap_temp >= 120 && cap_temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ct_c",
        "cap_temp >= 120 && cap_temp <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capillary inlet temp offset+100 in [120, 500] representing 20-400 C",
    );
}

#[test]
fn test_nanoesi_back_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bp_psi", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bp_a",
        "bp_psi >= 0 && bp_psi <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bp_c",
        "bp_psi >= 0 && bp_psi <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "back pressure in [0, 100] psi");
}

#[test]
fn test_nanoesi_emitter_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("emitter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "em_a",
        "emitter == 1 || emitter == 2 || emitter == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "em_c",
        "emitter >= 1 && emitter <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "emitter material 3-way (borosilicate/fused-silica/metal-coated)",
    );
}

#[test]
fn test_nanoesi_spray_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sm_a",
        "spray_mode == 1 || spray_mode == 2 || spray_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sm_c",
        "spray_mode >= 1 && spray_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spray mode 3-way (static/dynamic/chip-based)");
}

#[test]
fn test_nanoesi_polarity_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polarity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pol_a",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pol_c",
        "polarity >= 1 && polarity <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "polarity 3-way (positive/negative/switching)");
}

#[test]
fn test_nanoesi_auto_spray_optimization_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto spray optimization flag is boolean (0 or 1)");
}
