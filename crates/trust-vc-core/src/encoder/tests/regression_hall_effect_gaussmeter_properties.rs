// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_measurement_range_mt_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reading_mt", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "reading_mt == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if reading_mt >= 1 && reading_mt <= 3000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gaussmeter: 1500 mT in [1, 3000]");
}

#[test]
fn test_resolution_scaled_thousandths_mt() {
    // Resolution 0.001 mT scaled x1000 to integer 1
    let mut ctx = VerificationContext::new();
    for v in &["reading_x1000", "resolution_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("distinguishable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rd", "reading_x1000 == 1500001")); // 1500.001 mT
    ctx.push_obligation(ProofObligation::assume("res", "resolution_x1000 == 1")); // 0.001 mT
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "distinguishable == if resolution_x1000 >= 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "distinguishable == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "res_positive",
        "resolution_x1000 > 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gaussmeter resolution: 0.001 mT (x1000 = 1)");
}

#[test]
fn test_accuracy_scaled_hundredths_percent() {
    // Accuracy 0.05% scaled x100 to integer 5
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "max_accuracy_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("meets_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "accuracy_x100 == 5")); // 0.05%
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x100 == 10")); // 0.10% max
    ctx.push_obligation(ProofObligation::assume(
        "ms_def",
        "meets_spec == if accuracy_x100 <= max_accuracy_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "meets_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gaussmeter accuracy: 0.05% <= 0.10% spec");
}

#[test]
fn test_probe_type_three_way_disjunction() {
    // 1=transverse, 2=axial, 3=flexible
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pt", "probe_type == 2")); // axial
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "probe_type == 1 || probe_type == 2 || probe_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "probe type: axial (2) in {1,2,3}");
}

#[test]
fn test_display_digits_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("digits", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "digits == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if digits >= 4 && digits <= 6 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "display: 5 digits in [4, 6]");
}

#[test]
fn test_frequency_range_hz_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_hz", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // DC to 100 kHz bandwidth
    ctx.push_obligation(ProofObligation::assume("f", "freq_hz == 50000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if freq_hz <= 100000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency: 50000 Hz <= 100000 Hz max");
}

#[test]
fn test_operating_temp_offset_bounded() {
    // Real range -40 to +85 C, offset by +500 stored as 460 to 585
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "temp_offset == 525")); // 25 C + 500
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_offset >= 460 && temp_offset <= 585 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp: 25C (offset 525) in [460, 585]");
}

#[test]
fn test_output_type_three_way_disjunction() {
    // 1=analog, 2=USB, 3=RS-232
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ot", "output_type == 3")); // RS-232
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "output_type == 1 || output_type == 2 || output_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type: RS-232 (3) in {1,2,3}");
}

#[test]
fn test_sample_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_rate", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if sample_rate >= 1 && sample_rate <= 50000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample rate: 10000 S/s in [1, 50000]");
}

#[test]
fn test_auto_ranging_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_range", i32_ty());
    ctx.declare_var_typed("range_selected", u32_ty());
    ctx.declare_var_typed("reading_mt", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ar", "auto_range == 1")); // enabled
    ctx.push_obligation(ProofObligation::assume("rd", "reading_mt == 50"));
    // Auto-range selects low range (1) for small readings, high range (2) for large
    ctx.push_obligation(ProofObligation::assume(
        "rs_def",
        "range_selected == if auto_range == 1 { if reading_mt <= 300 { 1 } else { 2 } } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("low", "range_selected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-range: enabled, 50 mT -> low range (1)");
}
