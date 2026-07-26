// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_continuous_band_dryer_belt_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("belt_width", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_width_range",
        "belt_width >= 500 && belt_width <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_width_bounded",
        "belt_width >= 500 && belt_width <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt width must be between 500 and 3000 mm");
}

#[test]
fn test_continuous_band_dryer_belt_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("belt_length", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_length_range",
        "belt_length >= 2000 && belt_length <= 30000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_length_bounded",
        "belt_length >= 2000 && belt_length <= 30000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt length must be between 2000 and 30000 mm");
}

#[test]
fn test_continuous_band_dryer_belt_speed_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("belt_speed_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_speed_x100_range",
        "belt_speed_x100 >= 1 && belt_speed_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_speed_x100_bounded",
        "belt_speed_x100 >= 1 && belt_speed_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt speed x100 must be between 1 and 500 (0.01-5.00 m/min)",
    );
}

#[test]
fn test_continuous_band_dryer_drying_zones_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drying_zones", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drying_zones_range",
        "drying_zones >= 1 && drying_zones <= 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drying_zones_bounded",
        "drying_zones >= 1 && drying_zones <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of drying zones must be between 1 and 10");
}

#[test]
fn test_continuous_band_dryer_air_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_temp_offset100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "air_temp_offset100_range",
        "air_temp_offset100 >= 120 && air_temp_offset100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "air_temp_offset100_bounded",
        "air_temp_offset100 >= 120 && air_temp_offset100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air temperature offset+100 must be between 120 and 500 (20-400 C)",
    );
}

#[test]
fn test_continuous_band_dryer_bed_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bed_depth", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bed_depth_range",
        "bed_depth >= 10 && bed_depth <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bed_depth_bounded",
        "bed_depth >= 10 && bed_depth <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "material bed depth must be between 10 and 200 mm");
}

#[test]
fn test_continuous_band_dryer_heating_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heating_source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heating_source_range",
        "heating_source >= 1 && heating_source <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "heating_source_valid",
        "heating_source >= 1 && heating_source <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating source must be 1=electric, 2=steam, or 3=gas",
    );
}

#[test]
fn test_continuous_band_dryer_belt_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("belt_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_material_range",
        "belt_material >= 1 && belt_material <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_material_valid",
        "belt_material >= 1 && belt_material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt material must be 1=stainless-steel, 2=polyester, or 3=PTFE",
    );
}

#[test]
fn test_continuous_band_dryer_airflow_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("airflow_config", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "airflow_config_range",
        "airflow_config >= 1 && airflow_config <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "airflow_config_valid",
        "airflow_config >= 1 && airflow_config <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "airflow config must be 1=through-circulation, 2=over-bed, or 3=combined",
    );
}

#[test]
fn test_continuous_band_dryer_auto_belt_tracking_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_belt_tracking", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_belt_tracking_range",
        "auto_belt_tracking >= 0 && auto_belt_tracking <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_belt_tracking_valid",
        "auto_belt_tracking >= 0 && auto_belt_tracking <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto belt tracking flag must be 0=disabled or 1=enabled",
    );
}
