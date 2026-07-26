// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_rotary_drum_dryer_drum_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diameter_range",
        "diameter >= 500 && diameter <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diameter_bounded",
        "diameter >= 500 && diameter <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drum diameter must be between 500 and 3000 mm");
}

#[test]
fn test_rotary_drum_dryer_drum_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "length_range",
        "length >= 1000 && length <= 15000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "length_bounded",
        "length >= 1000 && length <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drum length must be between 1000 and 15000 mm");
}

#[test]
fn test_rotary_drum_dryer_rotation_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed_x10 >= 1 && speed_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed_x10 >= 1 && speed_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed x10 must be between 1 and 100");
}

#[test]
fn test_rotary_drum_dryer_feed_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "feed_rate_range",
        "feed_rate >= 10 && feed_rate <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "feed_rate_bounded",
        "feed_rate >= 10 && feed_rate <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate must be between 10 and 5000 kg/h");
}

#[test]
fn test_rotary_drum_dryer_discharge_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_offset >= 50 && temp_offset <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_offset >= 50 && temp_offset <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge temperature offset+100 must be between 50 and 350",
    );
}

#[test]
fn test_rotary_drum_dryer_inclination_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("incline_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "incline_range",
        "incline_x100 >= 50 && incline_x100 <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "incline_bounded",
        "incline_x100 >= 50 && incline_x100 <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inclination x100 must be between 50 and 700");
}

#[test]
fn test_rotary_drum_dryer_heating_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heating", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heating_range",
        "heating == 1 || heating == 2 || heating == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "heating_valid",
        "heating == 1 || heating == 2 || heating == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating type must be direct-fired, indirect, or steam-tube",
    );
}

#[test]
fn test_rotary_drum_dryer_flight_pattern_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flight", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flight_range",
        "flight == 1 || flight == 2 || flight == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flight_valid",
        "flight == 1 || flight == 2 || flight == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flight pattern must be straight, spiral, or combination",
    );
}

#[test]
fn test_rotary_drum_dryer_airflow_direction_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("airflow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "airflow_range",
        "airflow == 1 || airflow == 2 || airflow == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "airflow_valid",
        "airflow == 1 || airflow == 2 || airflow == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "airflow direction must be co-current, counter-current, or mixed",
    );
}

#[test]
fn test_rotary_drum_dryer_auto_feed_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_feed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_feed_range",
        "auto_feed == 0 || auto_feed == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_feed_valid",
        "auto_feed == 0 || auto_feed == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto feed control flag must be 0 (disabled) or 1 (enabled)",
    );
}
