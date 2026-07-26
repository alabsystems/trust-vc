// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_natural_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_x10", "freq_min", "freq_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Natural (resonant) frequency in Hz (×10): value 100 (10.0 Hz), range [10, 1000]
    ctx.push_obligation(ProofObligation::assume("nf_val", "freq_x10 == 100"));
    ctx.push_obligation(ProofObligation::assume("nf_min", "freq_min == 10"));
    ctx.push_obligation(ProofObligation::assume("nf_max", "freq_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "nf_in_range",
        "freq_x10 >= freq_min && freq_x10 <= freq_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "geophone natural frequency 10.0 Hz (100 x10) in [10, 1000]",
    );
}

#[test]
fn test_sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["sens_x100", "sens_min", "sens_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Sensitivity in V/m/s (×100): value 2800 (28.00 V/m/s), range [100, 10000]
    ctx.push_obligation(ProofObligation::assume("se_val", "sens_x100 == 2800"));
    ctx.push_obligation(ProofObligation::assume("se_min", "sens_min == 100"));
    ctx.push_obligation(ProofObligation::assume("se_max", "sens_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "se_in_range",
        "sens_x100 >= sens_min && sens_x100 <= sens_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "geophone sensitivity 28.00 V/m/s (2800 x100) in [100, 10000]",
    );
}

#[test]
fn test_coil_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["coil_ohm", "coil_min", "coil_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Coil resistance (impedance) in ohms: value 375, range [100, 10000]
    ctx.push_obligation(ProofObligation::assume("cr_val", "coil_ohm == 375"));
    ctx.push_obligation(ProofObligation::assume("cr_min", "coil_min == 100"));
    ctx.push_obligation(ProofObligation::assume("cr_max", "coil_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "cr_in_range",
        "coil_ohm >= coil_min && coil_ohm <= coil_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "geophone coil resistance 375 ohm in [100, 10000]");
}

#[test]
fn test_channel_count() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "ch_min", "ch_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Acquisition channel count: value 24, range [1, 1024]
    ctx.push_obligation(ProofObligation::assume("ch_val", "channels == 24"));
    ctx.push_obligation(ProofObligation::assume("ch_min", "ch_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ch_max", "ch_max == 1024"));
    ctx.push_obligation(ProofObligation::assert(
        "ch_in_range",
        "channels >= ch_min && channels <= ch_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "geophone 24 channels in [1, 1024]");
}

#[test]
fn test_geophone_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geo_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // Geophone type 3-way disjunction: 1=vertical, 2=horizontal, 3=omnidirectional
    ctx.push_obligation(ProofObligation::assume("gt_val", "geo_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "gt_def",
        "valid_type == if geo_type == 1 || geo_type == 2 || geo_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("gt_chk", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "geophone vertical (type 1) is valid 3-way type");
}

#[test]
fn test_sample_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sr_hz", u32_ty());
    ctx.declare_var_typed("valid_sr", i32_ty());
    // Sample rate 4-way non-sequential Hz: 500, 1000, 2000, 4000
    ctx.push_obligation(ProofObligation::assume("sr_val", "sr_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "sr_def",
        "valid_sr == if sr_hz == 500 || sr_hz == 1000 || sr_hz == 2000 || sr_hz == 4000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sr_chk", "valid_sr == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "geophone sample rate 1000 Hz is valid 4-way rate");
}

#[test]
fn test_dynamic_range() {
    let mut ctx = VerificationContext::new();
    for v in &["dyn_db", "dyn_min", "dyn_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Dynamic range in dB: value 120, range [90, 150]
    ctx.push_obligation(ProofObligation::assume("dr_val", "dyn_db == 120"));
    ctx.push_obligation(ProofObligation::assume("dr_min", "dyn_min == 90"));
    ctx.push_obligation(ProofObligation::assume("dr_max", "dyn_max == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "dr_in_range",
        "dyn_db >= dyn_min && dyn_db <= dyn_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "geophone dynamic range 120 dB in [90, 150]");
}

#[test]
fn test_operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating temperature offset +500: value 525 (25°C), range [460 (-40°C), 585 (85°C)]
    ctx.push_obligation(ProofObligation::assume("to_val", "temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assume("to_min", "temp_min == 460"));
    ctx.push_obligation(ProofObligation::assume("to_max", "temp_max == 585"));
    ctx.push_obligation(ProofObligation::assert(
        "to_in_range",
        "temp_offset >= temp_min && temp_offset <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "geophone 25°C (offset 525) in [-40°C, 85°C] range");
}

#[test]
fn test_spurious_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["spur_x10", "spur_min", "spur_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Spurious (parasitic) frequency in Hz (×10): value 1400 (140.0 Hz), range [500, 5000]
    ctx.push_obligation(ProofObligation::assume("sf_val", "spur_x10 == 1400"));
    ctx.push_obligation(ProofObligation::assume("sf_min", "spur_min == 500"));
    ctx.push_obligation(ProofObligation::assume("sf_max", "spur_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "sf_in_range",
        "spur_x10 >= spur_min && spur_x10 <= spur_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "geophone spurious frequency 140.0 Hz (1400 x10) in [500, 5000]",
    );
}

#[test]
fn test_waterproof_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("waterproof", i32_ty());
    ctx.declare_var_typed("is_sealed", i32_ty());
    // Waterproof boolean flag: 1=waterproof, 0=not waterproof
    ctx.push_obligation(ProofObligation::assume("wp_val", "waterproof == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "wp_def",
        "is_sealed == if waterproof == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("wp_chk", "is_sealed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "geophone waterproof enabled (flag=1)");
}
