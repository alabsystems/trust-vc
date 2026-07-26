// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_electrochemical_cell_voltage_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cell_mv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cv_a",
        "cell_mv >= 100 && cell_mv <= 2500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cv_c",
        "cell_mv >= 100 && cell_mv <= 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cell voltage x1000 in [100, 2500]");
}

#[test]
fn test_electrochemical_current_density_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("j_ma_cm2", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cd_a",
        "j_ma_cm2 >= 10 && j_ma_cm2 <= 30000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cd_c",
        "j_ma_cm2 >= 10 && j_ma_cm2 <= 30000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "current density in [10, 30000] mA/cm^2");
}

#[test]
fn test_electrochemical_membrane_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mem_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mt_a",
        "mem_temp >= 20 && mem_temp <= 120",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mt_c",
        "mem_temp >= 20 && mem_temp <= 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "membrane temperature in [20, 120] C");
}

#[test]
fn test_electrochemical_discharge_pressure_kpa_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p_out_kpa", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "p_out_kpa >= 100 && p_out_kpa <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "p_out_kpa >= 100 && p_out_kpa <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure in [100, 100000] kPa");
}

#[test]
fn test_electrochemical_h2_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("h2_flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hf_a",
        "h2_flow_x10 >= 1 && h2_flow_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hf_c",
        "h2_flow_x10 >= 1 && h2_flow_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "H2 flow x10 in [1, 5000]");
}

#[test]
fn test_electrochemical_humidity_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rh_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rh_a",
        "rh_x10 >= 300 && rh_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rh_c",
        "rh_x10 >= 300 && rh_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "membrane humidity x10 in [300, 1000]");
}

#[test]
fn test_electrochemical_membrane_material_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mem_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mm_a",
        "mem_mat == 1 || mem_mat == 2 || mem_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mm_c",
        "mem_mat == 1 || mem_mat == 2 || mem_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "membrane: Nafion, PBI, or sulfonated PEEK");
}

#[test]
fn test_electrochemical_catalyst_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("catalyst", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cat_a",
        "catalyst == 1 || catalyst == 2 || catalyst == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cat_c",
        "catalyst == 1 || catalyst == 2 || catalyst == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "catalyst: Pt/C, IrO2, or PtRu alloy");
}

#[test]
fn test_electrochemical_cooling_method_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cool_a",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cool_c",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling: air-cooled, liquid-cooled, or evaporative",
    );
}

#[test]
fn test_electrochemical_recirculation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("recirc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rc_a",
        "recirc == 0 || recirc == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rc_c",
        "recirc == 0 || recirc == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "recirculation flag is boolean");
}
