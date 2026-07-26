// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn horizontal_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["h_acc_mm", "max_h_acc_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("h_ok", i32_ty());
    // Horizontal accuracy in mm (RTK fixed)
    ctx.push_obligation(ProofObligation::assume("hm", "h_acc_mm == 8")); // 8mm
    ctx.push_obligation(ProofObligation::assume("mh", "max_h_acc_mm == 20")); // 20mm
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "h_ok == if h_acc_mm <= max_h_acc_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "h_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTK: 8mm horizontal accuracy ≤ 20mm max → OK");
}

#[test]
fn vertical_accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["v_acc_mm", "max_v_acc_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("v_ok", i32_ty());
    // Vertical accuracy in mm (RTK fixed)
    ctx.push_obligation(ProofObligation::assume("vm", "v_acc_mm == 15")); // 15mm
    ctx.push_obligation(ProofObligation::assume("mv", "max_v_acc_mm == 40")); // 40mm
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "v_ok == if v_acc_mm <= max_v_acc_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "v_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTK: 15mm vertical accuracy ≤ 40mm max → OK");
}

#[test]
fn fix_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fix", u32_ty());
    ctx.declare_var_typed("valid_fix", i32_ty());
    // RTK fix types: 1=no fix, 2=autonomous, 3=DGPS, 4=RTK float, 5=RTK fixed
    ctx.push_obligation(ProofObligation::assume("f", "fix == 5")); // RTK fixed
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_fix == if fix == 1 || fix == 2 || fix == 3 || fix == 4 || fix == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_fix == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTK: fixed is valid fix type");
}

#[test]
fn constellation_mask() {
    let mut ctx = VerificationContext::new();
    for v in &["constellations", "min_constellations"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("const_ok", i32_ty());
    // Number of active constellations (GPS, GLONASS, Galileo, BeiDou, QZSS, NavIC)
    ctx.push_obligation(ProofObligation::assume("c", "constellations == 4"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_constellations == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "const_ok == if constellations >= min_constellations { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "const_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTK: 4 constellations ≥ 1 min → OK");
}

#[test]
fn baseline_length() {
    let mut ctx = VerificationContext::new();
    for v in &["baseline_m", "max_baseline_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("base_ok", i32_ty());
    // Distance from base station to rover in meters
    ctx.push_obligation(ProofObligation::assume("bm", "baseline_m == 5000")); // 5 km
    ctx.push_obligation(ProofObligation::assume("mb", "max_baseline_m == 60000")); // 60 km
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "base_ok == if baseline_m <= max_baseline_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "base_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTK: 5km baseline ≤ 60km max → OK");
}

#[test]
fn update_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_hz", "min_rate_hz", "max_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Position update rate in Hz
    ctx.push_obligation(ProofObligation::assume("rh", "rate_hz == 20"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_rate_hz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rate_hz == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if rate_hz >= min_rate_hz && rate_hz <= max_rate_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTK: 20 Hz update in [1, 100] → OK");
}

#[test]
fn satellite_count() {
    let mut ctx = VerificationContext::new();
    for v in &["sats", "min_sats"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sat_ok", i32_ty());
    // Minimum satellites for RTK solution
    ctx.push_obligation(ProofObligation::assume("s", "sats == 18"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_sats == 5")); // min for RTK
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sat_ok == if sats >= min_sats { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sat_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTK: 18 satellites ≥ 5 min → OK");
}

#[test]
fn correction_age() {
    let mut ctx = VerificationContext::new();
    for v in &["age_sec", "max_age_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("age_ok", i32_ty());
    // Age of differential corrections in seconds
    ctx.push_obligation(ProofObligation::assume("as_val", "age_sec == 1"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_age_sec == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "age_ok == if age_sec <= max_age_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "age_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTK: 1s correction age ≤ 10s max → OK");
}

#[test]
fn initialization_time() {
    let mut ctx = VerificationContext::new();
    for v in &["init_sec", "max_init_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("init_ok", i32_ty());
    // Time to first RTK fix in seconds
    ctx.push_obligation(ProofObligation::assume("is", "init_sec == 30"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_init_sec == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "init_ok == if init_sec <= max_init_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "init_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTK: 30s initialization ≤ 120s max → OK");
}

#[test]
fn frequency_bands() {
    let mut ctx = VerificationContext::new();
    for v in &["bands", "min_bands"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("band_ok", i32_ty());
    // Number of frequency bands tracked (L1, L2, L5, etc.)
    ctx.push_obligation(ProofObligation::assume("b", "bands == 3")); // tri-frequency
    ctx.push_obligation(ProofObligation::assume("mb", "min_bands == 2")); // dual-freq min for RTK
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "band_ok == if bands >= min_bands { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "band_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTK: 3 frequency bands ≥ 2 min → OK");
}
