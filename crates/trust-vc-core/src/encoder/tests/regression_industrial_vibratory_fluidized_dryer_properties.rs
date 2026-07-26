// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_vibratory_fluid_dryer_deck_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("deck_length", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "deck_length_range",
        "deck_length >= 1000 && deck_length <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "deck_length_valid",
        "deck_length >= 1000 && deck_length <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "deck length must be between 1000 and 10000 mm");
}

#[test]
fn test_vibratory_fluid_dryer_deck_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("deck_width", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "deck_width_range",
        "deck_width >= 300 && deck_width <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "deck_width_valid",
        "deck_width >= 300 && deck_width <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "deck width must be between 300 and 3000 mm");
}

#[test]
fn test_vibratory_fluid_dryer_vibration_frequency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vibration_frequency_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vibration_frequency_x10_range",
        "vibration_frequency_x10 >= 50 && vibration_frequency_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vibration_frequency_x10_valid",
        "vibration_frequency_x10 >= 50 && vibration_frequency_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vibration frequency x10 must be between 50 and 500 (5.0-50.0 Hz)",
    );
}

#[test]
fn test_vibratory_fluid_dryer_amplitude_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("amplitude_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "amplitude_x100_range",
        "amplitude_x100 >= 10 && amplitude_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "amplitude_x100_valid",
        "amplitude_x100 >= 10 && amplitude_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vibration amplitude x100 must be between 10 and 500 (0.10-5.00 mm)",
    );
}

#[test]
fn test_vibratory_fluid_dryer_air_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_temp_offset100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "air_temp_offset100_range",
        "air_temp_offset100 >= 120 && air_temp_offset100 <= 450",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "air_temp_offset100_valid",
        "air_temp_offset100 >= 120 && air_temp_offset100 <= 450",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air temperature offset+100 must be between 120 and 450 (20-350 C)",
    );
}

#[test]
fn test_vibratory_fluid_dryer_bed_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bed_depth", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bed_depth_range",
        "bed_depth >= 20 && bed_depth <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bed_depth_valid",
        "bed_depth >= 20 && bed_depth <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fluidized bed depth must be between 20 and 300 mm");
}

#[test]
fn test_vibratory_fluid_dryer_vibration_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vibration_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vibration_mode_range",
        "vibration_mode >= 1 && vibration_mode <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vibration_mode_valid",
        "vibration_mode >= 1 && vibration_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vibration mode must be 1=linear, 2=circular, or 3=elliptical",
    );
}

#[test]
fn test_vibratory_fluid_dryer_deck_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("deck_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "deck_material_range",
        "deck_material >= 1 && deck_material <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "deck_material_valid",
        "deck_material >= 1 && deck_material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "deck material must be 1=stainless-steel, 2=carbon-steel, or 3=titanium",
    );
}

#[test]
fn test_vibratory_fluid_dryer_discharge_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discharge_type_range",
        "discharge_type >= 1 && discharge_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discharge_type_valid",
        "discharge_type >= 1 && discharge_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge type must be 1=overflow-weir, 2=underflow, or 3=end-discharge",
    );
}

#[test]
fn test_vibratory_fluid_dryer_auto_amplitude_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_amplitude_control", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_amplitude_control_range",
        "auto_amplitude_control >= 0 && auto_amplitude_control <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_amplitude_control_valid",
        "auto_amplitude_control >= 0 && auto_amplitude_control <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto amplitude control flag must be 0=disabled or 1=enabled",
    );
}
