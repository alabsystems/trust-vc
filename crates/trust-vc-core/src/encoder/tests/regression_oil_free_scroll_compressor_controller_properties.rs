// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_scroll_compressor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1000 && speed <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1000 && speed <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scroll speed must be between 1000 and 6000 RPM");
}

#[test]
fn test_scroll_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure_x10 >= 10 && pressure_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure_x10 >= 10 && pressure_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 must be between 10 and 100 (1.0-10.0 bar)",
    );
}

#[test]
fn test_scroll_compressor_free_air_delivery_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fad_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fad_range",
        "fad_x10 >= 1 && fad_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fad_bounded",
        "fad_x10 >= 1 && fad_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "free air delivery x10 must be between 1 and 10000 (0.1-1000.0 L/min)",
    );
}

#[test]
fn test_scroll_compressor_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power_x10 >= 1 && power_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power_x10 >= 1 && power_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motor power x10 must be between 1 and 5000 (0.1-500.0 kW)",
    );
}

#[test]
fn test_scroll_compressor_sound_level_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sound_db", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sound_range",
        "sound_db >= 40 && sound_db <= 85",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sound_bounded",
        "sound_db >= 40 && sound_db <= 85",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sound level must be between 40 and 85 dB");
}

#[test]
fn test_scroll_compressor_scroll_pairs_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scroll_pairs", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pairs_range",
        "scroll_pairs >= 1 && scroll_pairs <= 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pairs_bounded",
        "scroll_pairs >= 1 && scroll_pairs <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of scroll pairs must be between 1 and 4");
}

#[test]
fn test_scroll_compressor_tip_seal_material_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tip_seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tip_seal_valid",
        "tip_seal == 1 || tip_seal == 2 || tip_seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tip_seal_disjunction",
        "tip_seal == 1 || tip_seal == 2 || tip_seal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tip seal material must be PTFE(1), PEEK(2), or carbon-graphite(3)",
    );
}

#[test]
fn test_scroll_compressor_cooling_method_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cooling_valid",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cooling_disjunction",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling method must be air(1), water(2), or oil-free-coolant(3)",
    );
}

#[test]
fn test_scroll_compressor_drive_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drive_valid",
        "drive == 1 || drive == 2 || drive == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drive_disjunction",
        "drive == 1 || drive == 2 || drive == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive type must be direct(1), belt(2), or variable-speed(3)",
    );
}

#[test]
fn test_scroll_compressor_auto_condensate_drain_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_drain", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_drain_bool",
        "auto_drain == 0 || auto_drain == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_drain_valid",
        "auto_drain == 0 || auto_drain == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic condensate drain flag must be 0 (off) or 1 (on)",
    );
}
