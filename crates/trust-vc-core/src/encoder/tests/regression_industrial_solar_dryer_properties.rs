// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_solar_dryer_irradiance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("irr", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "irr >= 100 && irr <= 1200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "irr == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "irr >= 100 && irr <= 1200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "solar irradiance within valid range");
}

#[test]
fn test_solar_dryer_collector_area_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "area_x10 > 0 && area_x10 < 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "area_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "area_x10 > 0 && area_x10 < 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "solar collector area 500.0 m² within range");
}

#[test]
fn test_solar_dryer_air_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    // offset +100: temp_off=180 means 80°C
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "temp_off > 100 && temp_off < 400",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "temp_off == 180"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "temp_off > 100 && temp_off < 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solar dryer air temperature 80°C within offset range",
    );
}

#[test]
fn test_solar_dryer_airflow_rate_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "flow_x10 > 0 && flow_x10 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "flow_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "flow_x10 > 0 && flow_x10 < 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "solar dryer airflow rate 50.0 m³/min within range");
}

#[test]
fn test_solar_dryer_moisture_removal_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moist_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "moist_x100 > 0 && moist_x100 < 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "moist_x100 == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "moist_x100 > 0 && moist_x100 < 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solar dryer moisture removal 50.00 kg/h within range",
    );
}

#[test]
fn test_solar_dryer_number_of_trays_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trays", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "trays >= 1 && trays <= 50",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "trays == 12"));
    ctx.push_obligation(ProofObligation::assert(
        "bound",
        "trays >= 1 && trays <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "solar dryer tray count within valid range");
}

#[test]
fn test_solar_dryer_collector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctype", i32_ty());
    // 1=flat-plate, 2=evacuated-tube, 3=parabolic
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "ctype == 1 || ctype == 2 || ctype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "ctype == 1 || ctype == 2 || ctype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solar dryer collector type must be one of three options",
    );
}

#[test]
fn test_solar_dryer_drying_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    // 1=direct, 2=indirect, 3=mixed
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solar dryer drying mode must be one of three options",
    );
}

#[test]
fn test_solar_dryer_storage_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("storage", i32_ty());
    // 1=sensible-heat, 2=latent-heat, 3=none
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "storage == 1 || storage == 2 || storage == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "storage == 1 || storage == 2 || storage == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solar dryer storage method must be one of three options",
    );
}

#[test]
fn test_solar_dryer_auto_sun_tracking_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("boolean", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "sun_tracking",
        "if flag == 1 { 1 } else { 0 } >= 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "solar dryer automatic sun tracking boolean flag");
}
