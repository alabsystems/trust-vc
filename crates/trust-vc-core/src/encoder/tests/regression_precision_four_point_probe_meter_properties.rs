// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_four_point_probe_sheet_resistance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rs_mohm_sq_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sr_a",
        "rs_mohm_sq_x10 >= 1 && rs_mohm_sq_x10 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sr_c",
        "rs_mohm_sq_x10 >= 1 && rs_mohm_sq_x10 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sheet resistance x10 in [1, 100000]");
}

#[test]
fn test_four_point_probe_current_ua_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe_current_ua", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pc_a",
        "probe_current_ua >= 1 && probe_current_ua <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pc_c",
        "probe_current_ua >= 1 && probe_current_ua <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "probe current in [1, 10000] uA");
}

#[test]
fn test_four_point_probe_spacing_um_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spacing_um", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sp_a",
        "spacing_um >= 100 && spacing_um <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sp_c",
        "spacing_um >= 100 && spacing_um <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "probe spacing in [100, 5000] um");
}

#[test]
fn test_four_point_probe_thickness_um_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thickness_um", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "th_a",
        "thickness_um >= 1 && thickness_um <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "th_c",
        "thickness_um >= 1 && thickness_um <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "specimen thickness in [1, 10000] um");
}

#[test]
fn test_four_point_probe_contact_force_mn_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("force_mn", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cf_a",
        "force_mn >= 10 && force_mn <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cf_c",
        "force_mn >= 10 && force_mn <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "contact force in [10, 5000] mN");
}

#[test]
fn test_four_point_probe_voltage_uv_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_uv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mv_a",
        "voltage_uv >= 1 && voltage_uv <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mv_c",
        "voltage_uv >= 1 && voltage_uv <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement voltage in [1, 50000] uV");
}

#[test]
fn test_four_point_probe_arrangement_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("arrangement", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ar_a",
        "arrangement == 1 || arrangement == 2 || arrangement == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ar_c",
        "arrangement == 1 || arrangement == 2 || arrangement == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "arrangement: collinear, square, or rectangular");
}

#[test]
fn test_four_point_probe_tip_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tip_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tm_a",
        "tip_mat == 1 || tip_mat == 2 || tip_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tm_c",
        "tip_mat == 1 || tip_mat == 2 || tip_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "probe tip: tungsten carbide, osmium, or gold-plated",
    );
}

#[test]
fn test_four_point_probe_correction_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("correction", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "co_a",
        "correction == 1 || correction == 2 || correction == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "co_c",
        "correction == 1 || correction == 2 || correction == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "correction: infinite sheet, finite thickness, or edge proximity",
    );
}

#[test]
fn test_four_point_probe_auto_range_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ar_a2",
        "auto_range == 0 || auto_range == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ar_c2",
        "auto_range == 0 || auto_range == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-range flag is boolean");
}
