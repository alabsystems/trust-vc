// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn detection_range() {
    let mut ctx = VerificationContext::new();
    for v in &["range_mm", "min_range_mm", "max_range_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("range_ok", i32_ty());
    // Detection range in mm
    ctx.push_obligation(ProofObligation::assume("rm", "range_mm == 1000")); // 1m
    ctx.push_obligation(ProofObligation::assume("mn", "min_range_mm == 20")); // blind zone
    ctx.push_obligation(ProofObligation::assume("mx", "max_range_mm == 10000")); // 10m
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if range_mm >= min_range_mm && range_mm <= max_range_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "US Distance: 1m in [20mm, 10m] → OK");
}

#[test]
fn resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution_mm_x10", "min_res_mm_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Distance resolution in mm (×10 for 0.1mm)
    ctx.push_obligation(ProofObligation::assume("rx", "resolution_mm_x10 == 10")); // 1.0mm
    ctx.push_obligation(ProofObligation::assume("mr", "min_res_mm_x10 == 1")); // 0.1mm
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if resolution_mm_x10 >= min_res_mm_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "US Distance: 1.0mm resolution ≥ 0.1mm min → OK");
}

#[test]
fn operating_frequency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_khz", u32_ty());
    ctx.declare_var_typed("valid_freq", i32_ty());
    // Standard ultrasonic frequencies in kHz
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_freq == if freq_khz == 25 || freq_khz == 40 || freq_khz == 58 || freq_khz == 200 || freq_khz == 400 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_freq == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "US Distance: 40kHz is valid operating frequency");
}

#[test]
fn beam_angle() {
    let mut ctx = VerificationContext::new();
    for v in &["angle_x10", "min_angle_x10", "max_angle_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("angle_ok", i32_ty());
    // Beam cone half-angle in degrees (×10 for 0.1°)
    ctx.push_obligation(ProofObligation::assume("ax", "angle_x10 == 50")); // 5.0°
    ctx.push_obligation(ProofObligation::assume("mn", "min_angle_x10 == 10")); // 1.0°
    ctx.push_obligation(ProofObligation::assume("mx", "max_angle_x10 == 150")); // 15.0°
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "angle_ok == if angle_x10 >= min_angle_x10 && angle_x10 <= max_angle_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "angle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "US Distance: 5.0° beam in [1.0, 15.0] → OK");
}

#[test]
fn blind_zone() {
    let mut ctx = VerificationContext::new();
    for v in &["blind_mm", "max_blind_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("blind_ok", i32_ty());
    // Near-field dead zone in mm
    ctx.push_obligation(ProofObligation::assume("bm", "blind_mm == 20"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_blind_mm == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "blind_ok == if blind_mm <= max_blind_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "blind_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "US Distance: 20mm blind zone ≤ 200mm max → OK");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_ms", "max_resp_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resp_ok", i32_ty());
    // Measurement response time in ms
    ctx.push_obligation(ProofObligation::assume("rm", "resp_ms == 50"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_resp_ms == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if resp_ms <= max_resp_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "US Distance: 50ms response ≤ 500ms max → OK");
}

#[test]
fn output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // Output types: 1=analog (4-20mA), 2=analog (0-10V), 3=digital (PNP), 4=digital (NPN), 5=IO-Link
    ctx.push_obligation(ProofObligation::assume("o", "output == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_output == if output == 1 || output == 2 || output == 3 || output == 4 || output == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "US Distance: 4-20mA is valid output type");
}

#[test]
fn temperature_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature (offset +500): -25°C to 70°C
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520")); // 20°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 475")); // -25°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 570")); // 70°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "US Distance: 20°C in [-25, 70] → OK");
}

#[test]
fn protection_rating() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ip_rating", u32_ty());
    ctx.declare_var_typed("valid_ip", i32_ty());
    // IP ratings: 65=IP65, 67=IP67, 68=IP68, 69=IP69K
    ctx.push_obligation(ProofObligation::assume("ir", "ip_rating == 67"));
    ctx.push_obligation(ProofObligation::assume(
        "vi_def",
        "valid_ip == if ip_rating == 65 || ip_rating == 67 || ip_rating == 68 || ip_rating == 69 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ip == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "US Distance: IP67 is valid protection rating");
}

#[test]
fn repeat_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["repeat_mm_x10", "max_repeat_mm_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rep_ok", i32_ty());
    // Repeatability in mm (×10 for 0.1mm)
    ctx.push_obligation(ProofObligation::assume("rx", "repeat_mm_x10 == 5")); // 0.5mm
    ctx.push_obligation(ProofObligation::assume("mr", "max_repeat_mm_x10 == 20")); // 2.0mm
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rep_ok == if repeat_mm_x10 <= max_repeat_mm_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rep_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "US Distance: 0.5mm repeatability ≤ 2.0mm max → OK");
}
