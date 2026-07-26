// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ek_applied_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_v", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "av_a",
        "voltage_v >= 5 && voltage_v <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "av_c",
        "voltage_v >= 5 && voltage_v <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "applied voltage in [5, 200] V");
}

#[test]
fn test_ek_current_density_ma_cm2_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("j_ma_cm2", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cd_a",
        "j_ma_cm2 >= 1 && j_ma_cm2 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cd_c",
        "j_ma_cm2 >= 1 && j_ma_cm2 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "current density in [1, 500] mA/cm^2");
}

#[test]
fn test_ek_electrode_spacing_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spacing_mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "es_a",
        "spacing_mm >= 5 && spacing_mm <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "es_c",
        "spacing_mm >= 5 && spacing_mm <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "electrode spacing in [5, 500] mm");
}

#[test]
fn test_ek_initial_moisture_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mc_init_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "im_a",
        "mc_init_x10 >= 500 && mc_init_x10 <= 950",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "im_c",
        "mc_init_x10 >= 500 && mc_init_x10 <= 950",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "initial moisture x10 in [500, 950] representing 50.0-95.0%",
    );
}

#[test]
fn test_ek_treatment_time_min_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_min", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tt_a",
        "time_min >= 1 && time_min <= 480",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tt_c",
        "time_min >= 1 && time_min <= 480",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "treatment time in [1, 480] min (up to 8 hours)");
}

#[test]
fn test_ek_mechanical_pressure_kpa_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mech_kpa", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mp_a",
        "mech_kpa >= 0 && mech_kpa <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mp_c",
        "mech_kpa >= 0 && mech_kpa <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mechanical pressure in [0, 5000] kPa");
}

#[test]
fn test_ek_electrode_material_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("elec_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "em_a",
        "elec_mat == 1 || elec_mat == 2 || elec_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "em_c",
        "elec_mat == 1 || elec_mat == 2 || elec_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "electrode: stainless steel, titanium, or conductive polymer",
    );
}

#[test]
fn test_ek_sludge_type_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sludge", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "sludge == 1 || sludge == 2 || sludge == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "sludge == 1 || sludge == 2 || sludge == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sludge: municipal wastewater, mining tailings, or paper mill",
    );
}

#[test]
fn test_ek_configuration_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("config", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cf_a",
        "config == 1 || config == 2 || config == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cf_c",
        "config == 1 || config == 2 || config == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "configuration: belt press, filter press, or gravity belt",
    );
}

#[test]
fn test_ek_polarity_reversal_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reversal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pr_a",
        "reversal == 0 || reversal == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pr_c",
        "reversal == 0 || reversal == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "polarity reversal flag is boolean");
}
