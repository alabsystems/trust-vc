// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Ultrasonic thickness gauge properties:
// Non-destructive measurement of material thickness using ultrasound pulse-echo.

#[test]
fn test_measurement_range_bounded() {
    // Measurement range in ×100 mm: 50.00 mm = 5000, valid [10, 50000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rv", "range_x100 == 5000"));
    ctx.push_obligation(ProofObligation::assert("lower", "range_x100 >= 10"));
    ctx.push_obligation(ProofObligation::assert("upper", "range_x100 <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thickness range 50.00mm (×100) in [10, 50000]");
}

#[test]
fn test_resolution_bounded() {
    // Resolution in ×1000 mm: 0.010 mm = 10, valid [1, 100]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rv", "res_x1000 == 10"));
    ctx.push_obligation(ProofObligation::assert("lower", "res_x1000 >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "res_x1000 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 0.010mm (×1000) in [1, 100]");
}

#[test]
fn test_accuracy_bounded() {
    // Accuracy in ×1000 mm: 0.050 mm = 50, valid [5, 200]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume("av", "accuracy_x1000 == 50"));
    ctx.push_obligation(ProofObligation::assert("lower", "accuracy_x1000 >= 5"));
    ctx.push_obligation(ProofObligation::assert("upper", "accuracy_x1000 <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 0.050mm (×1000) in [5, 200]");
}

#[test]
fn test_probe_type_disjunction() {
    // Probe type: 1=single crystal, 2=dual element, 3=EMAT
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pt", "probe_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_probe",
        "probe_type == 1 || probe_type == 2 || probe_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "probe type dual element (2) in {1,2,3}");
}

#[test]
fn test_display_type_disjunction() {
    // Display type: 1=digits only, 2=A-scan, 3=B-scan
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("display_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dt", "display_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_display",
        "display_type == 1 || display_type == 2 || display_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "display type A-scan (2) in {1,2,3}");
}

#[test]
fn test_sound_velocity_bounded() {
    // Sound velocity in m/s: 5920 (steel), valid [1000, 12000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vv", "velocity == 5920"));
    ctx.push_obligation(ProofObligation::assert("lower", "velocity >= 1000"));
    ctx.push_obligation(ProofObligation::assert("upper", "velocity <= 12000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sound velocity 5920 m/s in [1000, 12000]");
}

#[test]
fn test_pulse_repetition_rate_bounded() {
    // Pulse repetition rate in Hz: 1000, valid [10, 5000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prr", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pv", "prr == 1000"));
    ctx.push_obligation(ProofObligation::assert("lower", "prr >= 10"));
    ctx.push_obligation(ProofObligation::assert("upper", "prr <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulse repetition rate 1000 Hz in [10, 5000]");
}

#[test]
fn test_communication_disjunction() {
    // Communication: 1=USB, 2=RS-232, 3=Bluetooth, 4=WiFi
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cv", "comm == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_comm",
        "comm == 1 || comm == 2 || comm == 3 || comm == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "communication USB (1) in {1,2,3,4}");
}

#[test]
fn test_operating_temp_offset() {
    // Operating temperature with +500 offset: 20°C → 520, valid [460 (-40°C), 570 (70°C)]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tv", "temp == 520"));
    ctx.push_obligation(ProofObligation::assert("lower", "temp >= 460"));
    ctx.push_obligation(ProofObligation::assert("upper", "temp <= 570"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 20°C (offset 520) in [460, 570]");
}

#[test]
fn test_through_coating_mode_boolean() {
    // Through-coating mode: boolean flag as i32 (1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fv", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "enabled",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "through-coating mode enabled (flag=1)");
}
