// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial pneumatic conveying dryer property verification.
// Encodes key parameters of a pneumatic conveying dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Conveying velocity (x10 m/s) — scaled at 0.1 m/s, bounded [1, 499].
/// 1 represents 0.1 m/s, 499 represents 49.9 m/s. Value 150 (15.0 m/s).
#[test]
fn test_pneumatic_conveying_dryer_conveying_velocity_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vel_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vel_val", "vel_x10 == 150"));
    ctx.push_obligation(ProofObligation::assert("vel_pos", "vel_x10 > 0"));
    ctx.push_obligation(ProofObligation::assert("vel_max", "vel_x10 < 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conveying velocity 15.0 m/s (150 x10) in (0, 500)");
}

/// Test 2: Inlet temperature offset +100 (deg C) — bounded (100, 900).
/// 200 represents 100 C, 800 represents 700 C. Value 450 (350 C).
#[test]
fn test_pneumatic_conveying_dryer_inlet_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_off == 450"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp_off > 100"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp_off < 900"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inlet temperature 350 C (offset 450) in (100, 900)",
    );
}

/// Test 3: Throughput (x10 kg/h) — scaled at 0.1 kg/h, bounded (0, 100000).
/// 500 represents 50.0 kg/h, 100000 represents 10000.0 kg/h. Value 5000 (500.0 kg/h).
#[test]
fn test_pneumatic_conveying_dryer_throughput_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rate_val", "rate_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert("rate_pos", "rate_x10 > 0"));
    ctx.push_obligation(ProofObligation::assert("rate_max", "rate_x10 < 100000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 500.0 kg/h (5000 x10) in (0, 100000)");
}

/// Test 4: Pipe diameter (x10 mm) — scaled at 0.1 mm, bounded (0, 10000).
/// 500 represents 50.0 mm, 10000 represents 1000.0 mm. Value 2000 (200.0 mm).
#[test]
fn test_pneumatic_conveying_dryer_pipe_diameter_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diam_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("diam_val", "diam_x10 == 2000"));
    ctx.push_obligation(ProofObligation::assert("diam_pos", "diam_x10 > 0"));
    ctx.push_obligation(ProofObligation::assert("diam_max", "diam_x10 < 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pipe diameter 200.0 mm (2000 x10) in (0, 10000)");
}

/// Test 5: Pressure drop (x100 kPa) — scaled at 0.01 kPa, bounded (0, 50000).
/// 100 represents 1.00 kPa, 50000 represents 500.00 kPa. Value 2500 (25.00 kPa).
#[test]
fn test_pneumatic_conveying_dryer_pressure_drop_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drop_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("drop_val", "drop_x100 == 2500"));
    ctx.push_obligation(ProofObligation::assert("drop_pos", "drop_x100 > 0"));
    ctx.push_obligation(ProofObligation::assert("drop_max", "drop_x100 < 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure drop 25.00 kPa (2500 x100) in (0, 50000)");
}

/// Test 6: Number of bends — bounded [1, 20], value 6.
#[test]
fn test_pneumatic_conveying_dryer_number_of_bends_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bends", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bends_val", "bends == 6"));
    ctx.push_obligation(ProofObligation::assert("bends_min", "bends >= 1"));
    ctx.push_obligation(ProofObligation::assert("bends_max", "bends <= 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of bends 6 in [1, 20]");
}

/// Test 7: Conveying mode — 3-way disjunction.
/// 1=dilute-phase, 2=dense-phase, 3=semi-dense. Value 1 (dilute-phase).
#[test]
fn test_pneumatic_conveying_dryer_conveying_mode_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_mode",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "conveying mode 1 (dilute-phase) is valid 3-way disjunction",
    );
}

/// Test 8: Material feed method — 3-way disjunction.
/// 1=rotary-valve, 2=blow-tank, 3=screw-feeder. Value 2 (blow-tank).
#[test]
fn test_pneumatic_conveying_dryer_material_feed_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed", u32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_feed",
        "feed == 1 || feed == 2 || feed == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "material feed 2 (blow-tank) is valid 3-way disjunction",
    );
}

/// Test 9: Separation method — 3-way disjunction.
/// 1=cyclone, 2=filter, 3=gravity. Value 1 (cyclone).
#[test]
fn test_pneumatic_conveying_dryer_separation_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sep", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sep_val", "sep == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_sep",
        "sep == 1 || sep == 2 || sep == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "separation method 1 (cyclone) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic moisture feedback — boolean flag using i32 with if/else pattern.
/// Flag 1 = moisture feedback enabled, fb_active = 1.
#[test]
fn test_pneumatic_conveying_dryer_auto_moisture_feedback_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fb_flag", i32_ty());
    ctx.declare_var_typed("fb_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "fb_flag == 0 || fb_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "fb_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "fb_def",
        "fb_active == if fb_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fb_enabled", "fb_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto moisture feedback flag activates moisture controller",
    );
}
