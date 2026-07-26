// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn multi_turn_count() {
    let mut ctx = VerificationContext::new();
    for v in &["turns", "max_turns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("turns_ok", i32_ty());
    // Multi-turn absolute encoder: tracks full revolutions
    ctx.push_obligation(ProofObligation::assume("t", "turns == 100"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_turns == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "turns_ok == if turns <= max_turns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "turns_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Resolver: 100 turns ≤ 4096 max → OK");
}

#[test]
fn single_turn_angle() {
    let mut ctx = VerificationContext::new();
    for v in &["angle_x100", "max_angle_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("angle_ok", i32_ty());
    // Single-turn angle: 0-359.99° (×100 for 0.01° resolution)
    ctx.push_obligation(ProofObligation::assume("ax", "angle_x100 == 18000")); // 180.00°
    ctx.push_obligation(ProofObligation::assume("ma", "max_angle_x100 == 35999"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "angle_ok == if angle_x100 <= max_angle_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "angle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Resolver: 180.00° ≤ 359.99° max → angle OK");
}

#[test]
fn excitation_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["exc_hz", "min_exc_hz", "max_exc_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("exc_ok", i32_ty());
    // Resolver excitation: typically 2-10 kHz
    ctx.push_obligation(ProofObligation::assume("eh", "exc_hz == 5000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_exc_hz == 2000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_exc_hz == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "exc_ok == if exc_hz >= min_exc_hz && exc_hz <= max_exc_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "exc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Resolver: 5kHz excitation in [2k, 10k] → OK");
}

#[test]
fn transformation_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["ratio_x100", "min_ratio_x100", "max_ratio_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ratio_ok", i32_ty());
    // Transformation ratio: sin/cos output vs excitation (×100, e.g., 50 = 0.50)
    ctx.push_obligation(ProofObligation::assume("rx", "ratio_x100 == 50")); // 0.50
    ctx.push_obligation(ProofObligation::assume("mn", "min_ratio_x100 == 30"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ratio_x100 == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ratio_ok == if ratio_x100 >= min_ratio_x100 && ratio_x100 <= max_ratio_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ratio_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Resolver: 0.50 ratio in [0.30, 0.80] → OK");
}

#[test]
fn signal_level() {
    let mut ctx = VerificationContext::new();
    for v in &["signal_mv", "min_signal_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sig_ok", i32_ty());
    // Output signal level must exceed noise threshold
    ctx.push_obligation(ProofObligation::assume("sm", "signal_mv == 2000"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_signal_mv == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sig_ok == if signal_mv >= min_signal_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sig_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Resolver: 2000mV signal ≥ 500mV min → OK");
}

#[test]
fn zero_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["offset_x10", "max_offset_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("off_ok", i32_ty());
    // Electrical zero offset (×10 for 0.1° resolution)
    ctx.push_obligation(ProofObligation::assume("ox", "offset_x10 == 5")); // 0.5°
    ctx.push_obligation(ProofObligation::assume("mo", "max_offset_x10 == 30")); // 3.0°
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "off_ok == if offset_x10 <= max_offset_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "off_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Resolver: 0.5° zero offset ≤ 3.0° max → OK");
}

#[test]
fn accuracy_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("class_arcmin", u32_ty());
    ctx.declare_var_typed("valid_class", i32_ty());
    // Resolver accuracy classes: 5, 10, 15, 20, 30 arcminutes
    ctx.push_obligation(ProofObligation::assume("ca", "class_arcmin == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_class == if class_arcmin == 5 || class_arcmin == 10 || class_arcmin == 15 || class_arcmin == 20 || class_arcmin == 30 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_class == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Resolver: 10 arcmin is a valid accuracy class");
}

#[test]
fn temperature_drift() {
    let mut ctx = VerificationContext::new();
    for v in &["drift_x10", "max_drift_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("drift_ok", i32_ty());
    // Temperature-induced drift (×10 for 0.1 arcmin/°C resolution)
    ctx.push_obligation(ProofObligation::assume("dx", "drift_x10 == 2")); // 0.2 arcmin/°C
    ctx.push_obligation(ProofObligation::assume("md", "max_drift_x10 == 10")); // 1.0 arcmin/°C
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "drift_ok == if drift_x10 <= max_drift_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "drift_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Resolver: 0.2 arcmin/°C drift ≤ 1.0 max → OK");
}

#[test]
fn speed_tracking() {
    let mut ctx = VerificationContext::new();
    for v in &["rpm", "max_rpm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("speed_ok", i32_ty());
    // Maximum trackable speed
    ctx.push_obligation(ProofObligation::assume("r", "rpm == 15000"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_rpm == 30000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "speed_ok == if rpm <= max_rpm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "speed_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Resolver: 15000 RPM ≤ 30000 max → speed OK");
}

#[test]
fn reference_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vref_mv", "target_mv", "tolerance_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ref_ok", i32_ty());
    // Excitation reference voltage (tolerance band)
    ctx.push_obligation(ProofObligation::assume("vm", "vref_mv == 7020"));
    ctx.push_obligation(ProofObligation::assume("tm", "target_mv == 7000"));
    ctx.push_obligation(ProofObligation::assume("tl", "tolerance_mv == 350")); // 5%
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ref_ok == if vref_mv >= target_mv - tolerance_mv && vref_mv <= target_mv + tolerance_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ref_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Resolver: 7.02V ref in 7.0V ± 5% → OK");
}
