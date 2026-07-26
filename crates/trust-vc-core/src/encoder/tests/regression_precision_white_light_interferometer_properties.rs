// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_wli_vertical_range_um_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("z_range_um", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vr_a",
        "z_range_um >= 1 && z_range_um <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vr_c",
        "z_range_um >= 1 && z_range_um <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vertical range in [1, 100000] um (1um-100mm)");
}

#[test]
fn test_wli_vertical_resolution_pm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("z_res_pm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "zr_a",
        "z_res_pm >= 1 && z_res_pm <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "zr_c",
        "z_res_pm >= 1 && z_res_pm <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vertical resolution in [1, 10000] pm (sub-angstrom to 10nm)",
    );
}

#[test]
fn test_wli_lateral_resolution_nm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("xy_res_nm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lr_a",
        "xy_res_nm >= 100 && xy_res_nm <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lr_c",
        "xy_res_nm >= 100 && xy_res_nm <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lateral resolution in [100, 50000] nm (0.1-50 um)");
}

#[test]
fn test_wli_field_of_view_um_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fov_um", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fv_a",
        "fov_um >= 50 && fov_um <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fv_c",
        "fov_um >= 50 && fov_um <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "field of view in [50, 50000] um");
}

#[test]
fn test_wli_scan_speed_um_per_sec_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ss_a",
        "scan_speed >= 1 && scan_speed <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ss_c",
        "scan_speed >= 1 && scan_speed <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan speed in [1, 10000] um/s");
}

#[test]
fn test_wli_magnification_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mag_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mg_a",
        "mag_x10 >= 10 && mag_x10 <= 1150",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mg_c",
        "mag_x10 >= 10 && mag_x10 <= 1150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "magnification x10 in [10, 1150] representing 1.0x-115.0x",
    );
}

#[test]
fn test_wli_objective_type_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("objective", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ob_a",
        "objective == 1 || objective == 2 || objective == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ob_c",
        "objective == 1 || objective == 2 || objective == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "objective: Michelson, Mirau, or Linnik");
}

#[test]
fn test_wli_light_source_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("light_src", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ls_a",
        "light_src == 1 || light_src == 2 || light_src == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ls_c",
        "light_src == 1 || light_src == 2 || light_src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "light source: white LED, halogen, or superluminescent diode",
    );
}

#[test]
fn test_wli_analysis_mode_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analysis", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "am_a",
        "analysis == 1 || analysis == 2 || analysis == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "am_c",
        "analysis == 1 || analysis == 2 || analysis == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analysis: VSI (vertical scanning), PSI (phase shifting), or ePSI (enhanced)",
    );
}

#[test]
fn test_wli_stitching_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stitching", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "stitching == 0 || stitching == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "stitching == 0 || stitching == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "image stitching flag is boolean");
}
