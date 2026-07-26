// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_impingement_belt_dryer_belt_speed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bs_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_speed_range",
        "bs_x10 >= 1 && bs_x10 <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_speed_positive",
        "bs_x10 >= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt speed at x10 m/min is always positive within operating range",
    );
}

#[test]
fn test_impingement_belt_dryer_air_jet_velocity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "velocity_range",
        "velocity >= 10 && velocity <= 80",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "velocity_bounded",
        "velocity >= 10 && velocity <= 80",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air jet velocity in m/s stays within operating bounds",
    );
}

#[test]
fn test_impingement_belt_dryer_air_temperature_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_offset_range",
        "temp_off >= 150 && temp_off <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_above_boiling",
        "temp_off >= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air temperature offset +100C is always above minimum drying threshold",
    );
}

#[test]
fn test_impingement_belt_dryer_belt_width() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "width_range",
        "width >= 300 && width <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "width_positive_and_bounded",
        "width >= 300 && width <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt width in mm stays within manufacturing limits",
    );
}

#[test]
fn test_impingement_belt_dryer_zone_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zones", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "zone_count_range",
        "zones >= 1 && zones <= 15",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_one_zone", "zones >= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dryer always has at least one heating zone");
}

#[test]
fn test_impingement_belt_dryer_product_thickness() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thick_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "thickness_range",
        "thick_x10 >= 1 && thick_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "thickness_positive",
        "thick_x10 >= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "product thickness at x10 mm is always positive");
}

#[test]
fn test_impingement_belt_dryer_nozzle_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nozzle", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nozzle_type_range",
        "nozzle == 1 || nozzle == 2 || nozzle == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nozzle_valid",
        "nozzle >= 1 && nozzle <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nozzle type is one of slot(1), round(2), or air-bar(3)",
    );
}

#[test]
fn test_impingement_belt_dryer_belt_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_material_range",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "material_valid",
        "material >= 1 && material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt material is one of stainless-mesh(1), PTFE-coated(2), or perforated-plate(3)",
    );
}

#[test]
fn test_impingement_belt_dryer_exhaust_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("exhaust", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "exhaust_mode_range",
        "exhaust == 1 || exhaust == 2 || exhaust == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "exhaust_valid",
        "exhaust >= 1 && exhaust <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "exhaust mode is one of top(1), bottom(2), or combined(3)",
    );
}

#[test]
fn test_impingement_belt_dryer_auto_moisture_control() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("amc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "amc_boolean",
        "amc == 0 || amc == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "amc_valid_flag",
        "amc >= 0 && amc <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto moisture control flag is a valid boolean (0 or 1)",
    );
}
