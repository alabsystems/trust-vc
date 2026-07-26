// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_frequency_range_low_hz() {
    let mut ctx = VerificationContext::new();
    for v in &["excitation_hz", "min_freq_hz", "max_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // ECT excitation frequency: 100 Hz within [10, 100000] Hz
    ctx.push_obligation(ProofObligation::assume("ef", "excitation_hz == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_hz == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_hz == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if excitation_hz >= min_freq_hz && excitation_hz <= max_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECT freq low: 100 Hz in [10, 100000]");
}

#[test]
fn test_frequency_range_high_khz() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_khz", "max_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bounded", i32_ty());
    // High-frequency ECT: 500 kHz within [100, 10000] kHz
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_khz == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_khz == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "bounded == if freq_khz >= min_khz && freq_khz <= max_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "bounded == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECT freq high: 500 kHz in [100, 10000]");
}

#[test]
fn test_probe_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // 1=pencil, 2=surface, 3=bolt-hole, 4=array
    ctx.push_obligation(ProofObligation::assume("pt", "probe_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if probe_type == 1 || probe_type == 2 || probe_type == 3 || probe_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECT probe: bolt-hole (3) in {1,2,3,4}");
}

#[test]
fn test_channel_count_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "min_channels", "max_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // ECT instrument channel count: 32 within [1, 128]
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 32"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_channels == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_channels == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if channels >= min_channels && channels <= max_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECT channels: 32 in [1, 128]");
}

#[test]
fn test_gain_amplification_db() {
    let mut ctx = VerificationContext::new();
    for v in &["gain_db", "min_gain_db", "max_gain_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Amplifier gain: 40 dB within [0, 100] dB
    ctx.push_obligation(ProofObligation::assume("g", "gain_db == 40"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_gain_db == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_gain_db == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if gain_db >= min_gain_db && gain_db <= max_gain_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECT gain: 40 dB in [0, 100]");
}

#[test]
fn test_inspection_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // 1=surface, 2=subsurface, 3=conductivity
    ctx.push_obligation(ProofObligation::assume("m", "mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if mode == 1 || mode == 2 || mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECT mode: subsurface (2) in {1,2,3}");
}

#[test]
fn test_scan_speed_traversal() {
    let mut ctx = VerificationContext::new();
    for v in &["speed_mm_s", "min_speed", "max_speed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Scan speed: 200 mm/s within [10, 5000] mm/s
    ctx.push_obligation(ProofObligation::assume("s", "speed_mm_s == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_speed == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_speed == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if speed_mm_s >= min_speed && speed_mm_s <= max_speed { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECT scan speed: 200 mm/s in [10, 5000]");
}

#[test]
fn test_defect_sensitivity_minimum_detectable() {
    let mut ctx = VerificationContext::new();
    for v in &["sensitivity_um", "min_sensitivity", "max_sensitivity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Minimum detectable defect: 500 um within [50, 10000] um
    ctx.push_obligation(ProofObligation::assume("s", "sensitivity_um == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_sensitivity == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_sensitivity == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if sensitivity_um >= min_sensitivity && sensitivity_um <= max_sensitivity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECT sensitivity: 500 um in [50, 10000]");
}

#[test]
fn test_data_storage_records() {
    let mut ctx = VerificationContext::new();
    for v in &["records", "min_records", "max_records"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Data storage capacity: 10000 records within [100, 500000]
    ctx.push_obligation(ProofObligation::assume("r", "records == 10000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_records == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_records == 500000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if records >= min_records && records <= max_records { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECT storage: 10000 records in [100, 500000]");
}

#[test]
fn test_differential_mode_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("differential_mode", i32_ty());
    ctx.declare_var_typed("output_type", u32_ty());
    // differential_mode=1 → output is differential (type 2), else absolute (type 1)
    ctx.push_obligation(ProofObligation::assume("dm", "differential_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ot_def",
        "output_type == if differential_mode == 1 { 2 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "output_type == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECT differential mode: flag=1 -> output type 2");
}
