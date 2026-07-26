// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Industrial drum coater controller property verification tests.

use super::*;

/// Drum diameter in cm, valid range 30-200.
#[test]
fn test_drum_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "diameter >= 30 && diameter <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "diameter == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "diameter >= 30 && diameter <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drum diameter 120cm within 30-200cm range");
}

/// Drum speed in x10 RPM (scaled integer), valid range 5-300 representing 0.5-30.0 RPM.
#[test]
fn test_drum_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drum_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "drum_speed >= 5 && drum_speed <= 300",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "drum_speed == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "drum_speed >= 5 && drum_speed <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drum speed 12.0RPM (x10=120) within 0.5-30.0RPM range",
    );
}

/// Spray rate in x100 mL/min (scaled integer), valid range 100-50000 representing 1.00-500.00 mL/min.
#[test]
fn test_spray_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "spray_rate >= 100 && spray_rate <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "spray_rate == 15000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "spray_rate >= 100 && spray_rate <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spray rate 150.00mL/min (x100=15000) within 1.00-500.00mL/min range",
    );
}

/// Inlet air temperature as offset+100 in degrees C, valid range 130-190 representing 30-90C.
#[test]
fn test_inlet_air_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "inlet_temp >= 130 && inlet_temp <= 190",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "inlet_temp == 170"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "inlet_temp >= 130 && inlet_temp <= 190",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inlet air temp 70C (offset+100=170) within 30-90C range",
    );
}

/// Coating pan load in kg, valid range 5-500.
#[test]
fn test_coating_pan_load_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pan_load", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "pan_load >= 5 && pan_load <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "pan_load == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "pan_load >= 5 && pan_load <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "coating pan load 250kg within 5-500kg range");
}

/// Number of spray guns, valid range 1-12.
#[test]
fn test_spray_gun_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gun_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "gun_count >= 1 && gun_count <= 12",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "gun_count == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "gun_count >= 1 && gun_count <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spray gun count 6 within 1-12 range");
}

/// Coating type: 1=sugar, 2=film, 3=enteric.
#[test]
fn test_coating_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coating_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "coating_type == 1 || coating_type == 2 || coating_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "coating_type == 1 || coating_type == 2 || coating_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "coating type is one of sugar(1), film(2), enteric(3)",
    );
}

/// Drum shape: 1=conventional, 2=perforated, 3=side-vented.
#[test]
fn test_drum_shape_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drum_shape", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "drum_shape == 1 || drum_shape == 2 || drum_shape == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "drum_shape == 1 || drum_shape == 2 || drum_shape == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drum shape is one of conventional(1), perforated(2), side-vented(3)",
    );
}

/// Air flow pattern: 1=concurrent, 2=countercurrent, 3=mixed.
#[test]
fn test_air_flow_pattern_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "air_flow == 1 || air_flow == 2 || air_flow == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "air_flow == 1 || air_flow == 2 || air_flow == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air flow pattern is one of concurrent(1), countercurrent(2), mixed(3)",
    );
}

/// Automatic weight gain monitoring flag: i32 boolean (0 or 1).
/// When flag==1, the if-then-else evaluates to 1 indicating monitoring is active.
#[test]
fn test_auto_weight_gain_monitoring_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_set", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "monitoring_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic weight gain monitoring active when flag is 1",
    );
}
