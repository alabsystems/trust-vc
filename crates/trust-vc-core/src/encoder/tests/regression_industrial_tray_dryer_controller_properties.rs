// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_tray_dryer_tray_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trays", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "trays_range",
        "trays >= 4 && trays <= 48",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "trays_bounded",
        "trays >= 4 && trays <= 48",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tray count should be bounded to 4-48");
}

#[test]
fn test_tray_dryer_tray_area_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_range",
        "area_x10 >= 5 && area_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_bounded",
        "area_x10 >= 5 && area_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tray area x10 should be bounded to 5-200 (0.5-20.0 m2)",
    );
}

#[test]
fn test_tray_dryer_air_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp >= 540 && temp <= 750",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 540 && temp <= 750",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air temp offset+500 should be bounded to 540-750 (40-250C)",
    );
}

#[test]
fn test_tray_dryer_air_velocity_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vel_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vel_range",
        "vel_x10 >= 5 && vel_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vel_bounded",
        "vel_x10 >= 5 && vel_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air velocity x10 should be bounded to 5-100 (0.5-10.0 m/s)",
    );
}

#[test]
fn test_tray_dryer_drying_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dt", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dt_range", "dt >= 1 && dt <= 72"));
    ctx.push_obligation(ProofObligation::assert("dt_bounded", "dt >= 1 && dt <= 72"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drying time should be bounded to 1-72 hours");
}

#[test]
fn test_tray_dryer_loading_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("load_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "load_range",
        "load_x10 >= 10 && load_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "load_bounded",
        "load_x10 >= 10 && load_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "loading x10 should be bounded to 10-500 (1.0-50.0 kg/m2)",
    );
}

#[test]
fn test_tray_dryer_airflow_pattern_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("af", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "af_valid",
        "af == 1 || af == 2 || af == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "af_bounded",
        "af == 1 || af == 2 || af == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "airflow pattern should be 1=horizontal, 2=vertical, or 3=cross-flow",
    );
}

#[test]
fn test_tray_dryer_heating_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heat_valid",
        "heat == 1 || heat == 2 || heat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "heat_bounded",
        "heat == 1 || heat == 2 || heat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating source should be 1=electric, 2=steam, or 3=hot water",
    );
}

#[test]
fn test_tray_dryer_tray_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_valid",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_bounded",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tray material should be 1=stainless steel, 2=aluminum, or 3=PTFE coated",
    );
}

#[test]
fn test_tray_dryer_vacuum_capable_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_valid", "vac == 0 || vac == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "vac_bounded",
        "vac == 0 || vac == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum capable flag should be 0 or 1");
}
