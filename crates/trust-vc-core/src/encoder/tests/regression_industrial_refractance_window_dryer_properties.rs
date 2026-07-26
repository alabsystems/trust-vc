// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_refractance_window_dryer_water_temperature_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "water_temp_a",
        "temp_off >= 170 && temp_off <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "water_temp_c",
        "temp_off >= 170 && temp_off <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "refractance window dryer water temperature offset +100 C",
    );
}

#[test]
fn test_refractance_window_dryer_film_thickness() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thick_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "film_thick_a",
        "thick_x10 >= 1 && thick_x10 <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "film_thick_c",
        "thick_x10 >= 1 && thick_x10 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refractance window dryer film thickness x10 mm");
}

#[test]
fn test_refractance_window_dryer_belt_speed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_speed_a",
        "speed_x100 >= 1 && speed_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_speed_c",
        "speed_x100 >= 1 && speed_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refractance window dryer belt speed x100 m/min");
}

#[test]
fn test_refractance_window_dryer_drying_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drying_time_a",
        "time_x10 >= 10 && time_x10 <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drying_time_c",
        "time_x10 >= 10 && time_x10 <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refractance window dryer drying time x10 seconds");
}

#[test]
fn test_refractance_window_dryer_belt_width() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_width_a",
        "width >= 200 && width <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_width_c",
        "width >= 200 && width <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refractance window dryer belt width mm");
}

#[test]
fn test_refractance_window_dryer_product_moisture() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moist_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "moisture_a",
        "moist_x10 >= 1 && moist_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "moisture_c",
        "moist_x10 >= 1 && moist_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "refractance window dryer product moisture x10 percent",
    );
}

#[test]
fn test_refractance_window_dryer_feed_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "feed_method_a",
        "method >= 1 && method <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "feed_method_c",
        "method >= 1 && method <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refractance window dryer feed method 3-way");
}

#[test]
fn test_refractance_window_dryer_belt_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_material_a",
        "material >= 1 && material <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_material_c",
        "material >= 1 && material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refractance window dryer belt material 3-way");
}

#[test]
fn test_refractance_window_dryer_collection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "collection_a",
        "mode >= 1 && mode <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "collection_c",
        "mode >= 1 && mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refractance window dryer collection 3-way");
}

#[test]
fn test_refractance_window_dryer_auto_temperature_control() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_ctrl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_temp_a",
        "auto_ctrl >= 0 && auto_ctrl <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_temp_c",
        "auto_ctrl >= 0 && auto_ctrl <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "refractance window dryer auto temperature control boolean",
    );
}
