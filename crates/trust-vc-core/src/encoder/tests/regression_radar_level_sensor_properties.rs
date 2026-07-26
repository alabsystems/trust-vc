// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    for v in &["range_mm", "max_range_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("range_ok", i32_ty());
    // Radar measurement range in mm
    ctx.push_obligation(ProofObligation::assume("rm", "range_mm == 15000")); // 15m
    ctx.push_obligation(ProofObligation::assume("mr", "max_range_mm == 80000")); // 80m
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if range_mm <= max_range_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar level: 15m range ≤ 80m max → OK");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_mm", "max_accuracy_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Measurement accuracy in mm
    ctx.push_obligation(ProofObligation::assume("am", "accuracy_mm == 2"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_mm == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_mm <= max_accuracy_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar level: 2mm accuracy ≤ 10mm max → OK");
}

#[test]
fn operating_frequency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_ghz", u32_ty());
    ctx.declare_var_typed("valid_freq", i32_ty());
    // Radar frequency bands: 6 GHz, 26 GHz, 80 GHz
    ctx.push_obligation(ProofObligation::assume("fg", "freq_ghz == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_freq == if freq_ghz == 6 || freq_ghz == 26 || freq_ghz == 80 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_freq == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar level: 80 GHz is valid frequency band");
}

#[test]
fn beam_angle() {
    let mut ctx = VerificationContext::new();
    for v in &["angle_x10", "max_angle_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("beam_ok", i32_ty());
    // Beam angle in degrees (×10 for 0.1°)
    ctx.push_obligation(ProofObligation::assume("ax", "angle_x10 == 30")); // 3.0°
    ctx.push_obligation(ProofObligation::assume("ma", "max_angle_x10 == 150")); // 15.0°
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "beam_ok == if angle_x10 <= max_angle_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "beam_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar level: 3.0° beam ≤ 15.0° max → OK");
}

#[test]
fn dead_zone() {
    let mut ctx = VerificationContext::new();
    for v in &["dead_mm", "max_dead_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dead_ok", i32_ty());
    // Near-field dead zone
    ctx.push_obligation(ProofObligation::assume("dm", "dead_mm == 100")); // 100mm
    ctx.push_obligation(ProofObligation::assume("md", "max_dead_mm == 500")); // 500mm
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dead_ok == if dead_mm <= max_dead_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dead_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar level: 100mm dead zone ≤ 500mm max → OK");
}

#[test]
fn process_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Process temperature: -40°C to +200°C (offset +500)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 550")); // 50°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 460")); // -40°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 700")); // 200°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar level: 50°C in [-40, 200] → OK");
}

#[test]
fn process_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar", "max_pressure_bar"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pb", "pressure_bar == 16"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pressure_bar == 160"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_bar <= max_pressure_bar { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar level: 16 bar ≤ 160 max → OK");
}

#[test]
fn echo_amplitude() {
    let mut ctx = VerificationContext::new();
    for v in &["echo_db", "min_echo_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("echo_ok", i32_ty());
    // Minimum echo amplitude for valid measurement
    ctx.push_obligation(ProofObligation::assume("ed", "echo_db == 20"));
    ctx.push_obligation(ProofObligation::assume("me", "min_echo_db == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "echo_ok == if echo_db >= min_echo_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "echo_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar level: 20dB echo ≥ 10dB min → OK");
}

#[test]
fn update_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_hz", "min_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Measurement update rate
    ctx.push_obligation(ProofObligation::assume("rh", "rate_hz == 5"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_rate_hz == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if rate_hz >= min_rate_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar level: 5Hz update ≥ 1Hz min → OK");
}

#[test]
fn antenna_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("antenna", u32_ty());
    ctx.declare_var_typed("valid_ant", i32_ty());
    // Antenna types: 1=horn, 2=rod, 3=drop, 4=parabolic, 5=lens
    ctx.push_obligation(ProofObligation::assume("a", "antenna == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_ant == if antenna == 1 || antenna == 2 || antenna == 3 || antenna == 4 || antenna == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ant == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Radar level: horn is valid antenna type");
}
