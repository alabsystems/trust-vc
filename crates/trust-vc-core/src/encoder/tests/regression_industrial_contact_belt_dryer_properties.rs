// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_contact_belt_dryer_plate_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "plate_temp_bounds",
        "temp_off >= 150 && temp_off <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "plate_temp_check",
        "temp_off >= 150 && temp_off <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "contact plate temp offset+100 should be bounded between 150 and 350",
    );
}

#[test]
fn test_contact_belt_dryer_belt_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_bounds",
        "speed_x10 >= 1 && speed_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_check",
        "speed_x10 >= 1 && speed_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt speed x10 should be bounded between 1 and 100 m/min",
    );
}

#[test]
fn test_contact_belt_dryer_pressure_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_bounds",
        "press_x100 >= 10 && press_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_check",
        "press_x100 >= 10 && press_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "contact pressure x100 should be bounded between 10 and 5000 kPa",
    );
}

#[test]
fn test_contact_belt_dryer_belt_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "width_bounds",
        "width >= 300 && width <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "width_check",
        "width >= 300 && width <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt width should be bounded between 300 and 3000 mm",
    );
}

#[test]
fn test_contact_belt_dryer_product_thickness_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thick_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "thickness_bounds",
        "thick_x10 >= 1 && thick_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "thickness_check",
        "thick_x10 >= 1 && thick_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "product thickness x10 should be bounded between 1 and 200 mm",
    );
}

#[test]
fn test_contact_belt_dryer_drying_time_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_bounds",
        "time_x10 >= 10 && time_x10 <= 1200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "time_check",
        "time_x10 >= 10 && time_x10 <= 1200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drying time x10 should be bounded between 10 and 1200 min",
    );
}

#[test]
fn test_contact_belt_dryer_heat_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heat_source",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "heat_source_check",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heat source should be steam, electric, or thermal-oil",
    );
}

#[test]
fn test_contact_belt_dryer_belt_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("belt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_material",
        "belt == 1 || belt == 2 || belt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_material_check",
        "belt == 1 || belt == 2 || belt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt material should be stainless, PTFE, or silicone",
    );
}

#[test]
fn test_contact_belt_dryer_feed_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "feed_method",
        "feed == 1 || feed == 2 || feed == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "feed_method_check",
        "feed == 1 || feed == 2 || feed == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "feed method should be roller, doctor-blade, or gravity",
    );
}

#[test]
fn test_contact_belt_dryer_auto_pressure_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_pressure_boolean",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_pressure_check",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto pressure control flag should be 0 or 1");
}
