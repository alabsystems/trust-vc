// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_vfb_dryer_vibration_frequency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vib_freq_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vf_a",
        "vib_freq_x10 >= 50 && vib_freq_x10 <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vf_c",
        "vib_freq_x10 >= 50 && vib_freq_x10 <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vibration frequency x10 in [50, 1500] representing 5.0-150.0 Hz",
    );
}

#[test]
fn test_vfb_dryer_vibration_amplitude_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("amp_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "amp_a",
        "amp_x100 >= 10 && amp_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "amp_c",
        "amp_x100 >= 10 && amp_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vibration amplitude x100 in [10, 5000] representing 0.10-50.00 mm",
    );
}

#[test]
fn test_vfb_dryer_air_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_a",
        "air_temp >= 120 && air_temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_c",
        "air_temp >= 120 && air_temp <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air temp offset+100 in [120, 500] representing 20-400 C",
    );
}

#[test]
fn test_vfb_dryer_bed_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bed_mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bd_a",
        "bed_mm >= 10 && bed_mm <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bd_c",
        "bed_mm >= 10 && bed_mm <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bed depth in [10, 500] mm");
}

#[test]
fn test_vfb_dryer_air_velocity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vel_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vel_a",
        "vel_x100 >= 10 && vel_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vel_c",
        "vel_x100 >= 10 && vel_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air velocity x100 in [10, 5000] representing 0.10-50.00 m/s",
    );
}

#[test]
fn test_vfb_dryer_residence_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_s", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rt_a",
        "res_s >= 30 && res_s <= 7200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rt_c",
        "res_s >= 30 && res_s <= 7200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residence time in [30, 7200] seconds");
}

#[test]
fn test_vfb_dryer_vibration_pattern_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pattern", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pat_a",
        "pattern == 1 || pattern == 2 || pattern == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pat_c",
        "pattern >= 1 && pattern <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vibration pattern 3-way (linear/circular/elliptical)",
    );
}

#[test]
fn test_vfb_dryer_deck_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("deck", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "deck_a",
        "deck == 1 || deck == 2 || deck == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("deck_c", "deck >= 1 && deck <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "deck material 3-way (perforated-steel/mesh/sintered-plate)",
    );
}

#[test]
fn test_vfb_dryer_heating_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heat_a",
        "heat == 1 || heat == 2 || heat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("heat_c", "heat >= 1 && heat <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating method 3-way (direct-gas/steam-coil/electric)",
    );
}

#[test]
fn test_vfb_dryer_exhaust_recirculation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "exhaust recirculation flag is boolean (0 or 1)");
}
