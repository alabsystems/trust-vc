// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_nanoindent_max_load_un_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("load_un", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ml_a",
        "load_un >= 1 && load_un <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ml_c",
        "load_un >= 1 && load_un <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max load in [1, 500000] uN (1uN-500mN)");
}

#[test]
fn test_nanoindent_depth_nm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_nm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dn_a",
        "depth_nm >= 1 && depth_nm <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dn_c",
        "depth_nm >= 1 && depth_nm <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "indentation depth in [1, 100000] nm (1nm-100um)");
}

#[test]
fn test_nanoindent_load_resolution_nn_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("load_res_nn", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lr_a",
        "load_res_nn >= 1 && load_res_nn <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lr_c",
        "load_res_nn >= 1 && load_res_nn <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "load resolution in [1, 10000] nN");
}

#[test]
fn test_nanoindent_displacement_resolution_pm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_res_pm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dr_a",
        "disp_res_pm >= 1 && disp_res_pm <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dr_c",
        "disp_res_pm >= 1 && disp_res_pm <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement resolution in [1, 10000] pm");
}

#[test]
fn test_nanoindent_loading_rate_un_per_s_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_un_s", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rt_a",
        "rate_un_s >= 1 && rate_un_s <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rt_c",
        "rate_un_s >= 1 && rate_un_s <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "loading rate in [1, 100000] uN/s");
}

#[test]
fn test_nanoindent_thermal_drift_pm_per_s_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drift_pm_s", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "td_a",
        "drift_pm_s >= 1 && drift_pm_s <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "td_c",
        "drift_pm_s >= 1 && drift_pm_s <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermal drift in [1, 5000] pm/s");
}

#[test]
fn test_nanoindent_tip_geometry_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tip_geom", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tg_a",
        "tip_geom == 1 || tip_geom == 2 || tip_geom == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tg_c",
        "tip_geom == 1 || tip_geom == 2 || tip_geom == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tip geometry: Berkovich, cube corner, or spherical",
    );
}

#[test]
fn test_nanoindent_test_mode_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("test_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tm_a",
        "test_mode == 1 || test_mode == 2 || test_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tm_c",
        "test_mode == 1 || test_mode == 2 || test_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test mode: quasi-static, CSM (continuous stiffness), or creep",
    );
}

#[test]
fn test_nanoindent_tip_material_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tip_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tp_a",
        "tip_mat == 1 || tip_mat == 2 || tip_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tp_c",
        "tip_mat == 1 || tip_mat == 2 || tip_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tip material: diamond, sapphire, or tungsten carbide",
    );
}

#[test]
fn test_nanoindent_csm_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("csm_on", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cm_a",
        "csm_on == 0 || csm_on == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cm_c",
        "csm_on == 0 || csm_on == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CSM overlay flag is boolean");
}
