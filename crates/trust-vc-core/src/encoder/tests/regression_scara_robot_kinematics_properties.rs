// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn arm_reach() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reach_mm", u32_ty());
    ctx.declare_var_typed("reach_ok", i32_ty());
    // Max reach radius in mm: 600mm, valid range 100-1200mm
    ctx.push_obligation(ProofObligation::assume("val", "reach_mm == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "reach_ok == if reach_mm >= 100 && reach_mm <= 1200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "reach_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCARA: 600mm arm reach in [100, 1200]");
}

#[test]
fn axes_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("axes", u32_ty());
    ctx.declare_var_typed("valid_axes", i32_ty());
    // Number of axes: 4 (typical SCARA), valid options: 3, 4, or 5
    ctx.push_obligation(ProofObligation::assume("val", "axes == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_axes == if axes == 3 || axes == 4 || axes == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_axes == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCARA: 4 axes is valid (3/4/5)");
}

#[test]
fn repeatability() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("repeat_um", u32_ty());
    ctx.declare_var_typed("repeat_ok", i32_ty());
    // Repeatability in micrometers: 20um, max 100um
    ctx.push_obligation(ProofObligation::assume("val", "repeat_um == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "repeat_ok == if repeat_um <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "repeat_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCARA: 20um repeatability within 100um max");
}

#[test]
fn max_payload() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("payload_g", u32_ty());
    ctx.declare_var_typed("payload_ok", i32_ty());
    // Payload capacity in grams: 5000g (5kg), valid range 100-50000g
    ctx.push_obligation(ProofObligation::assume("val", "payload_g == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "payload_ok == if payload_g >= 100 && payload_g <= 50000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "payload_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCARA: 5000g (5kg) payload in [100, 50000]");
}

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycle_ms", u32_ty());
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // Pick-and-place cycle time in ms: 400ms, max 2000ms
    ctx.push_obligation(ProofObligation::assume("val", "cycle_ms == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "cycle_ok == if cycle_ms <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCARA: 400ms cycle time within 2000ms max");
}

#[test]
fn z_stroke() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_mm", u32_ty());
    ctx.declare_var_typed("stroke_ok", i32_ty());
    // Vertical stroke in mm: 200mm, valid range 50-500mm
    ctx.push_obligation(ProofObligation::assume("val", "stroke_mm == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "stroke_ok == if stroke_mm >= 50 && stroke_mm <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "stroke_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCARA: 200mm Z-stroke in [50, 500]");
}

#[test]
fn max_speed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_mm_s", u32_ty());
    ctx.declare_var_typed("speed_ok", i32_ty());
    // Max tip speed in mm/s: 8000mm/s, valid range 1000-20000mm/s
    ctx.push_obligation(ProofObligation::assume("val", "speed_mm_s == 8000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "speed_ok == if speed_mm_s >= 1000 && speed_mm_s <= 20000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "speed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCARA: 8000mm/s tip speed in [1000, 20000]");
}

#[test]
fn motor_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mtype", u32_ty());
    ctx.declare_var_typed("valid_motor", i32_ty());
    // 1=stepper, 2=servo (AC), 3=direct drive
    ctx.push_obligation(ProofObligation::assume("val", "mtype == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_motor == if mtype == 1 || mtype == 2 || mtype == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_motor == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCARA: servo AC (2) is valid motor type (1/2/3)");
}

#[test]
fn encoder_bits() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bits", u32_ty());
    ctx.declare_var_typed("bits_ok", i32_ty());
    // Encoder resolution in bits: 17-bit, valid range 10-23 bits
    ctx.push_obligation(ProofObligation::assume("val", "bits == 17"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "bits_ok == if bits >= 10 && bits <= 23 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "bits_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCARA: 17-bit encoder resolution in [10, 23]");
}

#[test]
fn ip_rating() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rating", u32_ty());
    ctx.declare_var_typed("valid_ip", i32_ty());
    // IP protection rating: 20=IP20, 40=IP40, 65=IP65
    ctx.push_obligation(ProofObligation::assume("val", "rating == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "vi_def",
        "valid_ip == if rating == 20 || rating == 40 || rating == 65 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_ip == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SCARA: IP40 (40) is valid IP rating (20/40/65)");
}
