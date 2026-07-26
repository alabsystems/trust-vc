// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn position_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_cm", "max_accuracy_cm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Horizontal position accuracy in centimeters
    ctx.push_obligation(ProofObligation::assume("ac", "accuracy_cm == 250")); // 2.5m
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_cm == 500")); // 5.0m
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_cm <= max_accuracy_cm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPS: 2.5m accuracy ≤ 5.0m max → OK");
}

#[test]
fn satellite_count() {
    let mut ctx = VerificationContext::new();
    for v in &["sat_count", "min_sats"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sat_ok", i32_ty());
    // Minimum satellites for valid fix
    ctx.push_obligation(ProofObligation::assume("sc", "sat_count == 8"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_sats == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sat_ok == if sat_count >= min_sats { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sat_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPS: 8 satellites ≥ 4 min → OK");
}

#[test]
fn hdop_value() {
    let mut ctx = VerificationContext::new();
    for v in &["hdop_x10", "max_hdop_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hdop_ok", i32_ty());
    // Horizontal dilution of precision (×10 for 0.1 precision)
    ctx.push_obligation(ProofObligation::assume("hx", "hdop_x10 == 12")); // 1.2
    ctx.push_obligation(ProofObligation::assume("mh", "max_hdop_x10 == 50")); // 5.0
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hdop_ok == if hdop_x10 <= max_hdop_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hdop_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPS: HDOP 1.2 ≤ 5.0 max → OK");
}

#[test]
fn fix_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fix_mode", u32_ty());
    ctx.declare_var_typed("valid_fix", i32_ty());
    // Fix types: 0=none, 1=2D, 2=3D, 3=DGPS, 4=RTK-fixed, 5=RTK-float
    ctx.push_obligation(ProofObligation::assume("fm", "fix_mode == 2")); // 3D fix
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_fix == if fix_mode == 1 || fix_mode == 2 || fix_mode == 3 || fix_mode == 4 || fix_mode == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_fix == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPS: 3D fix is a valid fix type");
}

#[test]
fn update_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_hz", "min_rate_hz", "max_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Position update rate
    ctx.push_obligation(ProofObligation::assume("rh", "rate_hz == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_rate_hz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rate_hz == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if rate_hz >= min_rate_hz && rate_hz <= max_rate_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPS: 10Hz update rate in [1, 20] → OK");
}

#[test]
fn cold_start_time() {
    let mut ctx = VerificationContext::new();
    for v in &["ttff_sec", "max_ttff_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ttff_ok", i32_ty());
    // Time to first fix (cold start) in seconds
    ctx.push_obligation(ProofObligation::assume("ts", "ttff_sec == 30"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_ttff_sec == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "ttff_ok == if ttff_sec <= max_ttff_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ttff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPS: 30s cold TTFF ≤ 60s max → OK");
}

#[test]
fn constellation_support() {
    let mut ctx = VerificationContext::new();
    for v in &["constellations", "min_constellations"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("const_ok", i32_ty());
    // Number of GNSS constellations (GPS, GLONASS, Galileo, BeiDou)
    ctx.push_obligation(ProofObligation::assume("c", "constellations == 4"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_constellations == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "const_ok == if constellations >= min_constellations { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "const_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPS: 4 constellations ≥ 2 min → OK");
}

#[test]
fn velocity_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["vel_acc_cmps", "max_vel_acc_cmps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vel_ok", i32_ty());
    // Velocity accuracy in cm/s
    ctx.push_obligation(ProofObligation::assume("va", "vel_acc_cmps == 5")); // 0.05 m/s
    ctx.push_obligation(ProofObligation::assume("mv", "max_vel_acc_cmps == 10")); // 0.10 m/s
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vel_ok == if vel_acc_cmps <= max_vel_acc_cmps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPS: 5 cm/s velocity accuracy ≤ 10 max → OK");
}

#[test]
fn elevation_mask() {
    let mut ctx = VerificationContext::new();
    for v in &["mask_deg", "min_mask_deg", "max_mask_deg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mask_ok", i32_ty());
    // Elevation mask angle in degrees
    ctx.push_obligation(ProofObligation::assume("md", "mask_deg == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_mask_deg == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_mask_deg == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mask_ok == if mask_deg >= min_mask_deg && mask_deg <= max_mask_deg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mask_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPS: 10° elevation mask in [5, 30] → OK");
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "min_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ch_ok", i32_ty());
    // Hardware tracking channels
    ctx.push_obligation(ProofObligation::assume("c", "channels == 72"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_channels == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "ch_ok == if channels >= min_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ch_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GPS: 72 channels ≥ 32 min → OK");
}
