// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_freeze_dryer_shelf_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shelf_t_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "shelf_t_off >= 440 && shelf_t_off <= 560",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "shelf_t_off >= 440 && shelf_t_off <= 560",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shelf temp +500 offset in [440, 560] representing -60 to +60 C",
    );
}

#[test]
fn test_freeze_dryer_chamber_pressure_mtorr_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_mt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cp_a",
        "pressure_mt >= 10 && pressure_mt <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cp_c",
        "pressure_mt >= 10 && pressure_mt <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber pressure in [10, 5000] mTorr");
}

#[test]
fn test_freeze_dryer_condenser_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond_t_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ct_a",
        "cond_t_off >= 410 && cond_t_off <= 460",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ct_c",
        "cond_t_off >= 410 && cond_t_off <= 460",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "condenser temp +500 offset in [410, 460] representing -90 to -40 C",
    );
}

#[test]
fn test_freeze_dryer_sublimation_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sub_rate_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sr_a",
        "sub_rate_x100 >= 1 && sub_rate_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sr_c",
        "sub_rate_x100 >= 1 && sub_rate_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sublimation rate x100 in [1, 5000] representing 0.01-50.00 kg/hr/m^2",
    );
}

#[test]
fn test_freeze_dryer_product_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prod_t_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pt_a",
        "prod_t_off >= 460 && prod_t_off <= 530",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pt_c",
        "prod_t_off >= 460 && prod_t_off <= 530",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "product temp +500 offset in [460, 530] representing -40 to +30 C",
    );
}

#[test]
fn test_freeze_dryer_residual_moisture_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moisture_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rm_a",
        "moisture_x100 >= 10 && moisture_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rm_c",
        "moisture_x100 >= 10 && moisture_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "residual moisture x100 in [10, 1000] representing 0.10-10.00%",
    );
}

#[test]
fn test_freeze_dryer_drying_phase_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ph_a",
        "phase == 1 || phase == 2 || phase == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ph_c",
        "phase == 1 || phase == 2 || phase == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "phase: freezing, primary drying, or secondary drying",
    );
}

#[test]
fn test_freeze_dryer_vial_format_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vial_fmt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vf_a",
        "vial_fmt == 1 || vial_fmt == 2 || vial_fmt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vf_c",
        "vial_fmt == 1 || vial_fmt == 2 || vial_fmt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vial format: glass vial, tray, or bulk pan");
}

#[test]
fn test_freeze_dryer_vacuum_system_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac_sys", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vs_a",
        "vac_sys == 1 || vac_sys == 2 || vac_sys == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vs_c",
        "vac_sys == 1 || vac_sys == 2 || vac_sys == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum system: rotary vane, scroll, or diaphragm");
}

#[test]
fn test_freeze_dryer_stoppering_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stoppering", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sp_a",
        "stoppering == 0 || stoppering == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sp_c",
        "stoppering == 0 || stoppering == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "in-situ stoppering flag is boolean");
}
