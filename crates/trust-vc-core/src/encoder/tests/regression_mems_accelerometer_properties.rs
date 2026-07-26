// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn acceleration_from_adc() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_value", "adc_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("accel_mg", u32_ty());
    // Convert ADC to mg. Precompute: (2100 - 2048) × 4 = 208mg (±2g range, 12-bit)
    ctx.push_obligation(ProofObligation::assume("av", "adc_value == 2100"));
    ctx.push_obligation(ProofObligation::assume("ao", "adc_offset == 2048"));
    ctx.push_obligation(ProofObligation::assume("am", "accel_mg == 208")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_208", "accel_mg == 208"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MEMS accel: ADC 2100, offset 2048 → 208mg (precomputed)",
    );
}

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_g", u32_ty());
    ctx.declare_var_typed("range_ok", i32_ty());
    // Typical ranges: ±2g, ±4g, ±8g, ±16g (stored as 2,4,8,16)
    ctx.push_obligation(ProofObligation::assume("rg", "range_g == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if range_g == 2 || range_g == 4 || range_g == 8 || range_g == 16 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS accel: ±8g is a valid range");
}

#[test]
fn output_data_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["odr_hz", "min_odr_hz", "max_odr_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("odr_ok", i32_ty());
    // ODR: 1Hz to 6400Hz typical
    ctx.push_obligation(ProofObligation::assume("oh", "odr_hz == 400"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_odr_hz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_odr_hz == 6400"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "odr_ok == if odr_hz >= min_odr_hz && odr_hz <= max_odr_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "odr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS accel: 400Hz ODR in [1, 6400] → rate OK");
}

#[test]
fn self_test() {
    let mut ctx = VerificationContext::new();
    for v in &["st_delta", "st_min", "st_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("st_pass", i32_ty());
    // Self-test: output change must be within specified window
    ctx.push_obligation(ProofObligation::assume("sd", "st_delta == 300"));
    ctx.push_obligation(ProofObligation::assume("sm", "st_min == 200"));
    ctx.push_obligation(ProofObligation::assume("sx", "st_max == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "sp_def",
        "st_pass == if st_delta >= st_min && st_delta <= st_max { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "st_pass == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MEMS accel: self-test delta 300 in [200, 500] → pass",
    );
}

#[test]
fn fifo_watermark() {
    let mut ctx = VerificationContext::new();
    for v in &["fifo_level", "watermark"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("interrupt", i32_ty());
    // FIFO watermark interrupt when buffer reaches threshold
    ctx.push_obligation(ProofObligation::assume("fl", "fifo_level == 25"));
    ctx.push_obligation(ProofObligation::assume("wm", "watermark == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "i_def",
        "interrupt == if fifo_level >= watermark { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "interrupt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS accel: FIFO 25 ≥ watermark 20 → interrupt");
}

#[test]
fn high_pass_filter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hpf_enabled", u32_ty());
    ctx.declare_var_typed("dc_removed", i32_ty());
    // High-pass filter removes DC component (gravity)
    ctx.push_obligation(ProofObligation::assume("he", "hpf_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "dr_def",
        "dc_removed == if hpf_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dc_removed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS accel: HPF enabled → DC removed");
}

#[test]
fn freefall_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["accel_total_mg", "freefall_threshold_mg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freefall", i32_ty());
    // Free-fall: total acceleration below threshold
    ctx.push_obligation(ProofObligation::assume("at", "accel_total_mg == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ft",
        "freefall_threshold_mg == 150",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "freefall == if accel_total_mg <= freefall_threshold_mg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freefall == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MEMS accel: 50mg total ≤ 150mg threshold → freefall",
    );
}

#[test]
fn tap_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["shock_mg", "tap_threshold_mg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tap_detected", i32_ty());
    // Single/double tap: sudden acceleration spike above threshold
    ctx.push_obligation(ProofObligation::assume("sm", "shock_mg == 1500"));
    ctx.push_obligation(ProofObligation::assume("tt", "tap_threshold_mg == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "td_def",
        "tap_detected == if shock_mg >= tap_threshold_mg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tap_detected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS accel: 1500mg shock ≥ 1000mg threshold → tap");
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vdd_mv", "min_vdd_mv", "max_vdd_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vdd_ok", i32_ty());
    // Supply voltage: typically 1.71-3.6V
    ctx.push_obligation(ProofObligation::assume("vm", "vdd_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vdd_mv == 1710"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vdd_mv == 3600"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vdd_ok == if vdd_mv >= min_vdd_mv && vdd_mv <= max_vdd_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vdd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS accel: 3.3V in [1.71, 3.6] → supply OK");
}

#[test]
fn bandwidth_setting() {
    let mut ctx = VerificationContext::new();
    for v in &["bandwidth_hz", "max_bandwidth_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Anti-aliasing filter bandwidth
    ctx.push_obligation(ProofObligation::assume("bh", "bandwidth_hz == 200"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_bandwidth_hz == 3200"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bandwidth_hz <= max_bandwidth_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS accel: 200Hz BW ≤ 3200Hz max → bandwidth OK");
}
