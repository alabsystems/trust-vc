// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_operating_frequency_ghz_x100() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_x100", "min_freq_x100", "max_freq_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Operating frequency in GHz (x100): 2415 = 24.15 GHz (K/Ka band)
    ctx.push_obligation(ProofObligation::assume("fv", "freq_x100 == 2415"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_x100 == 900"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_x100 == 7700"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_x100 >= min_freq_x100 && freq_x100 <= max_freq_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar speed: 24.15 GHz in [9.00, 77.00] GHz -> OK");
}

#[test]
fn test_speed_range_kmh() {
    let mut ctx = VerificationContext::new();
    for v in &["max_velocity_kmh", "min_velocity_kmh", "max_allowed_kmh"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("speed_ok", i32_ty());
    // Maximum measurable velocity in km/h
    ctx.push_obligation(ProofObligation::assume("sv", "max_velocity_kmh == 300"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_velocity_kmh == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_allowed_kmh == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "speed_ok == if max_velocity_kmh >= min_velocity_kmh && max_velocity_kmh <= max_allowed_kmh { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "speed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar speed: 300 km/h in [10, 500] -> OK");
}

#[test]
fn test_accuracy_x10_kmh() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x10", "min_accuracy_x10", "max_accuracy_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy in km/h (x10): 10 = 1.0 km/h
    ctx.push_obligation(ProofObligation::assume("av", "accuracy_x10 == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_accuracy_x10 == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_accuracy_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x10 >= min_accuracy_x10 && accuracy_x10 <= max_accuracy_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Radar speed: 1.0 km/h accuracy in [0.5, 5.0] -> OK",
    );
}

#[test]
fn test_beam_width_x10_deg() {
    let mut ctx = VerificationContext::new();
    for v in &["beam_x10", "min_beam_x10", "max_beam_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("beam_ok", i32_ty());
    // Antenna beam width in degrees (x10): 50 = 5.0 degrees
    ctx.push_obligation(ProofObligation::assume("bv", "beam_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_beam_x10 == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_beam_x10 == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "beam_ok == if beam_x10 >= min_beam_x10 && beam_x10 <= max_beam_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "beam_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar speed: 5.0 deg beam in [2.0, 20.0] -> OK");
}

#[test]
fn test_detection_range_m() {
    let mut ctx = VerificationContext::new();
    for v in &["range_m", "min_range_m", "max_range_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("range_ok", i32_ty());
    // Maximum detection range in meters
    ctx.push_obligation(ProofObligation::assume("rv", "range_m == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_range_m == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_range_m == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if range_m >= min_range_m && range_m <= max_range_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar speed: 200m range in [10, 1000] -> OK");
}

#[test]
fn test_target_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("target_type", u32_ty());
    ctx.declare_var_typed("valid_target", i32_ty());
    // Target types: 1=vehicle, 2=pedestrian, 3=industrial
    ctx.push_obligation(ProofObligation::assume("tt", "target_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_target == if target_type == 1 || target_type == 2 || target_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_target == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar speed: vehicle is valid target type");
}

#[test]
fn test_output_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // Output types: 1=analog, 2=serial, 3=relay, 4=IO-Link
    ctx.push_obligation(ProofObligation::assume("ot", "output_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_output == if output_type == 1 || output_type == 2 || output_type == 3 || output_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar speed: serial is valid output type");
}

#[test]
fn test_mounting_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mounting", u32_ty());
    ctx.declare_var_typed("valid_mount", i32_ty());
    // Mounting types: 1=overhead, 2=side-fire, 3=portable
    ctx.push_obligation(ProofObligation::assume("mt", "mounting == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mount == if mounting == 1 || mounting == 2 || mounting == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mount == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar speed: overhead is valid mounting type");
}

#[test]
fn test_operating_temp_offset_500() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature: -40 to 85 C (offset +500). 525 = 25 C, 460 = -40 C, 585 = 85 C
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 460"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 585"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar speed: 25 C in [-40, 85] C -> OK");
}

#[test]
fn test_multi_target_tracking_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("multi_target", i32_ty());
    ctx.declare_var_typed("tracking_active", i32_ty());
    // Boolean flag: multi-target tracking enabled (1) or disabled (0)
    ctx.push_obligation(ProofObligation::assume("mt", "multi_target == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ta_def",
        "tracking_active == if multi_target == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tracking_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Radar speed: multi-target tracking enabled -> active",
    );
}
