// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_detection_limit_ppb() {
    // IC sensitivity: detection limit in parts per billion
    let mut ctx = VerificationContext::new();
    for v in &["detection_limit", "min_limit", "max_limit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dl", "detection_limit == 1"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_limit == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_limit == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if detection_limit >= min_limit && detection_limit <= max_limit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IC detection limit: 1 ppb in [0, 100]");
}

#[test]
fn test_flow_rate_ml_per_min() {
    // Eluent flow rate in mL/min scaled by 100: 100 = 1.00 mL/min
    let mut ctx = VerificationContext::new();
    for v in &["flow_rate", "min_flow", "max_flow"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_flow == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_flow == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if flow_rate >= min_flow && flow_rate <= max_flow { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IC flow rate: 100 (1.00 mL/min) in [10, 500]");
}

#[test]
fn test_detector_type_disjunction() {
    // IC detector: 1=conductivity, 2=UV, 3=amperometric
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dt", "detector_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if detector_type == 1 || detector_type == 2 || detector_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IC detector: conductivity (1) is valid");
}

#[test]
fn test_suppressor_type_disjunction() {
    // IC suppressor: 1=chemical, 2=electrolytic, 3=membrane
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("suppressor_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "suppressor_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if suppressor_type == 1 || suppressor_type == 2 || suppressor_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IC suppressor: electrolytic (2) is valid");
}

#[test]
fn test_column_length_mm() {
    // IC separation column length in mm
    let mut ctx = VerificationContext::new();
    for v in &["column_length", "min_length", "max_length"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cl", "column_length == 250"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_length == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_length == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if column_length >= min_length && column_length <= max_length { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IC column: 250 mm in [50, 500]");
}

#[test]
fn test_pressure_max_kpa() {
    // IC pump pressure limit in kPa
    let mut ctx = VerificationContext::new();
    for v in &["pressure_max", "min_pressure", "max_pressure"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pm", "pressure_max == 35000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pressure == 5000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pressure == 70000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if pressure_max >= min_pressure && pressure_max <= max_pressure { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IC pressure: 35000 kPa in [5000, 70000]");
}

#[test]
fn test_sample_volume_ul() {
    // IC injection sample volume in microliters
    let mut ctx = VerificationContext::new();
    for v in &["sample_volume", "min_volume", "max_volume"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sv", "sample_volume == 25"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_volume == 5"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_volume == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if sample_volume >= min_volume && sample_volume <= max_volume { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IC sample volume: 25 uL in [5, 500]");
}

#[test]
fn test_channel_count() {
    // IC detector channel count
    let mut ctx = VerificationContext::new();
    for v in &["channel_count", "min_channels", "max_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cc", "channel_count == 2"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_channels == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_channels == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if channel_count >= min_channels && channel_count <= max_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IC channels: 2 in [1, 4]");
}

#[test]
fn test_run_time_seconds() {
    // IC analysis run time in seconds
    let mut ctx = VerificationContext::new();
    for v in &["run_time", "min_time", "max_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rt", "run_time == 1200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_time == 120"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_time == 3600"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if run_time >= min_time && run_time <= max_time { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IC run time: 1200 s in [120, 3600]");
}

#[test]
fn test_autosampler_boolean_flag() {
    // IC autosampler present flag (i32 boolean: 1=yes, 0=no)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_autosampler", i32_ty());
    ctx.declare_var_typed("automated", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ha", "has_autosampler == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "automated == if has_autosampler == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "automated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IC autosampler: flag=1 → automated");
}
