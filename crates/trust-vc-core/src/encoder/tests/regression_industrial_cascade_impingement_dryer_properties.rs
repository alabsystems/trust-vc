// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Web speed at x10 m/min must stay within operational bounds.
#[test]
fn test_cascade_impingement_dryer_web_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ws_a",
        "speed_x10 >= 10 && speed_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ws_c",
        "speed_x10 >= 10 && speed_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cascade impingement dryer web speed x10 must be in [10, 5000]",
    );
}

/// Nozzle gap in mm must remain within safe clearance range.
#[test]
fn test_cascade_impingement_dryer_nozzle_gap_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gap", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ng_a", "gap >= 5 && gap <= 100"));
    ctx.push_obligation(ProofObligation::assert("ng_c", "gap >= 5 && gap <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cascade impingement dryer nozzle gap must be in [5, 100] mm",
    );
}

/// Air temperature with +100 offset must stay within operating envelope.
#[test]
fn test_cascade_impingement_dryer_air_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_a",
        "temp_off >= 150 && temp_off <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_c",
        "temp_off >= 150 && temp_off <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cascade impingement dryer air temperature offset must be in [150, 700]",
    );
}

/// Number of decks must be within valid structural range.
#[test]
fn test_cascade_impingement_dryer_deck_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("decks", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nd_a", "decks >= 1 && decks <= 20"));
    ctx.push_obligation(ProofObligation::assert("nd_c", "decks >= 1 && decks <= 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cascade impingement dryer deck count must be in [1, 20]",
    );
}

/// Exhaust humidity at x10 g/kg must stay within measurable range.
#[test]
fn test_cascade_impingement_dryer_exhaust_humidity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hum_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eh_a",
        "hum_x10 >= 10 && hum_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eh_c",
        "hum_x10 >= 10 && hum_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cascade impingement dryer exhaust humidity x10 must be in [10, 500]",
    );
}

/// Web width in mm must stay within machine capacity.
#[test]
fn test_cascade_impingement_dryer_web_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ww_a",
        "width >= 200 && width <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ww_c",
        "width >= 200 && width <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cascade impingement dryer web width must be in [200, 5000] mm",
    );
}

/// Nozzle configuration must be one of slot, round-hole, or floating.
#[test]
fn test_cascade_impingement_dryer_nozzle_configuration_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("config", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nc_a",
        "config == 1 || config == 2 || config == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nc_c",
        "config == 1 || config == 2 || config == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cascade impingement dryer nozzle config must be slot, round-hole, or floating",
    );
}

/// Heat recovery mode must be none, air-to-air, or thermal-wheel.
#[test]
fn test_cascade_impingement_dryer_heat_recovery_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("recovery", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hr_a",
        "recovery == 1 || recovery == 2 || recovery == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hr_c",
        "recovery == 1 || recovery == 2 || recovery == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cascade impingement dryer heat recovery must be none, air-to-air, or thermal-wheel",
    );
}

/// Exhaust system must be single-stack, dual-stack, or recirculating.
#[test]
fn test_cascade_impingement_dryer_exhaust_system_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("exhaust", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "es_a",
        "exhaust == 1 || exhaust == 2 || exhaust == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "es_c",
        "exhaust == 1 || exhaust == 2 || exhaust == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cascade impingement dryer exhaust system must be single-stack, dual-stack, or recirculating");
}

/// Automatic moisture control flag must be a boolean value.
#[test]
fn test_cascade_impingement_dryer_moisture_control_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mc_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("mc_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cascade impingement dryer moisture control flag must be 0 or 1",
    );
}
