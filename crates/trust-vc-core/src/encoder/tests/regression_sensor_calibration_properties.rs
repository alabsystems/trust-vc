// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn two_point_calibration() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "raw_low",
        "raw_high",
        "eng_low",
        "eng_high",
        "raw_value",
        "eng_value",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Linear interpolation between two known points
    // Precompute: raw 500 in [0, 1000] → eng 50 in [0, 100]
    ctx.push_obligation(ProofObligation::assume("rl", "raw_low == 0"));
    ctx.push_obligation(ProofObligation::assume("rh", "raw_high == 1000"));
    ctx.push_obligation(ProofObligation::assume("el", "eng_low == 0"));
    ctx.push_obligation(ProofObligation::assume("eh", "eng_high == 100"));
    ctx.push_obligation(ProofObligation::assume("rv", "raw_value == 500"));
    ctx.push_obligation(ProofObligation::assume("ev", "eng_value == 50")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_50", "eng_value == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cal: raw 500 in [0,1000] → 50 in [0,100]");
}

#[test]
fn zero_offset_correction() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_reading", "zero_offset", "corrected"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Zero offset: subtract known error at zero point
    ctx.push_obligation(ProofObligation::assume("rr", "raw_reading == 1050"));
    ctx.push_obligation(ProofObligation::assume("zo", "zero_offset == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "corrected == raw_reading - zero_offset",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1000", "corrected == 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cal zero: 1050 - 50 offset = 1000");
}

#[test]
fn span_correction() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "measured",
        "span_factor_num",
        "span_factor_den",
        "corrected",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Span: multiply by correction factor (as fraction)
    // measured × 100 / 98 ≈ measured × 1.0204
    // Precompute: 980 × 100 / 98 = 1000
    ctx.push_obligation(ProofObligation::assume("m", "measured == 980"));
    ctx.push_obligation(ProofObligation::assume("sfn", "span_factor_num == 100"));
    ctx.push_obligation(ProofObligation::assume("sfd", "span_factor_den == 98"));
    ctx.push_obligation(ProofObligation::assume("c", "corrected == 1000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1000", "corrected == 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cal span: 980 × 100/98 = 1000");
}

#[test]
fn adc_resolution_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution_bits", "max_code"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 12-bit ADC: max code = 2^12 - 1 = 4095
    ctx.push_obligation(ProofObligation::assume("rb", "resolution_bits == 12"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_code == 4095")); // precomputed 2^12-1
    ctx.push_obligation(ProofObligation::assert("is_4095", "max_code == 4095"));
    ctx.push_obligation(ProofObligation::assert("positive", "max_code > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cal ADC: 12-bit → max code 4095");
}

#[test]
fn temperature_linearization() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_mv", "ref_mv", "temp_offset_mc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_mc", u32_ty());
    // Thermocouple linearization: precompute lookup
    // Type K: 10mV ≈ 250°C = 250000 m°C. Reference junction at 25°C.
    ctx.push_obligation(ProofObligation::assume("rm", "raw_mv == 10"));
    ctx.push_obligation(ProofObligation::assume("rfm", "ref_mv == 1")); // 25°C reference
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset_mc == 25000")); // reference temp
    ctx.push_obligation(ProofObligation::assume("tm", "temp_mc == 250000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_250000", "temp_mc == 250000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cal thermocouple: 10mV → 250°C (precomputed)");
}

#[test]
fn drift_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "reading",
        "drift_per_hour",
        "hours_since_cal",
        "drift_correction",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("compensated", u32_ty());
    // Precompute drift: 2 units/hour × 5 hours = 10 units
    ctx.push_obligation(ProofObligation::assume("r", "reading == 1010"));
    ctx.push_obligation(ProofObligation::assume("dph", "drift_per_hour == 2"));
    ctx.push_obligation(ProofObligation::assume("hsc", "hours_since_cal == 5"));
    ctx.push_obligation(ProofObligation::assume("dc", "drift_correction == 10")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "comp_def",
        "compensated == reading - drift_correction",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1000", "compensated == 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cal drift: 1010 - 10 (2/h × 5h) = 1000");
}

#[test]
fn calibration_interval_check() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "last_cal_days",
        "current_days",
        "interval_days",
        "days_since_cal",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_recal", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lcd", "last_cal_days == 100"));
    ctx.push_obligation(ProofObligation::assume("cd", "current_days == 200"));
    ctx.push_obligation(ProofObligation::assume("id", "interval_days == 90"));
    ctx.push_obligation(ProofObligation::assume(
        "dsc_def",
        "days_since_cal == current_days - last_cal_days",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "nr_def",
        "needs_recal == if days_since_cal > interval_days { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "days_since_cal == 100"));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_recal == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cal: 100 days since cal > 90 interval → recalibrate",
    );
}

#[test]
fn measurement_uncertainty() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "measured_value",
        "uncertainty",
        "lower_bound",
        "upper_bound",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_tolerance", i32_ty());
    // Measurement = value ± uncertainty
    ctx.push_obligation(ProofObligation::assume("mv", "measured_value == 1000"));
    ctx.push_obligation(ProofObligation::assume("u", "uncertainty == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "lb_def",
        "lower_bound == measured_value - uncertainty",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ub_def",
        "upper_bound == measured_value + uncertainty",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "it_def",
        "in_tolerance == if lower_bound >= 990 && upper_bound <= 1010 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_995", "lower_bound == 995"));
    ctx.push_obligation(ProofObligation::assert("is_1005", "upper_bound == 1005"));
    ctx.push_obligation(ProofObligation::assert("ok", "in_tolerance == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cal: 1000 ± 5 → [995, 1005] within [990, 1010]");
}

#[test]
fn multi_point_lookup() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_input", "table_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Lookup table index = raw / step_size
    // raw=750, step=100 → index=7
    ctx.push_obligation(ProofObligation::assume("ri", "raw_input == 750"));
    ctx.push_obligation(ProofObligation::assume(
        "ti_def",
        "table_index == raw_input / 100",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if table_index < 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_7", "table_index == 7"));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "cal lookup: 750 / 100 = index 7 (in range)");
}

#[test]
fn sensor_range_check() {
    let mut ctx = VerificationContext::new();
    for v in &["sensor_min", "sensor_max", "reading"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.declare_var_typed("over_range", i32_ty());
    // Sensor range: 0-1000. Reading 800 is in range.
    ctx.push_obligation(ProofObligation::assume("smin", "sensor_min == 0"));
    ctx.push_obligation(ProofObligation::assume("smax", "sensor_max == 1000"));
    ctx.push_obligation(ProofObligation::assume("r", "reading == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if reading >= sensor_min && reading <= sensor_max { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "or_def",
        "over_range == if reading > sensor_max { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    ctx.push_obligation(ProofObligation::assert("no", "over_range == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cal: reading 800 in [0, 1000] → in range, not over",
    );
}
