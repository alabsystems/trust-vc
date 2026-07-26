// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn cold_junction_compensation() {
    let mut ctx = VerificationContext::new();
    for v in &["hot_junction_uv", "cold_junction_uv", "compensated_uv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Total EMF = hot_junction - cold_junction (both positive offsets)
    // Cold junction at 25°C ≈ 1000μV for Type K, hot at 500°C ≈ 20644μV
    ctx.push_obligation(ProofObligation::assume("hj", "hot_junction_uv == 20644"));
    ctx.push_obligation(ProofObligation::assume("cj", "cold_junction_uv == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "cu_def",
        "compensated_uv == hot_junction_uv - cold_junction_uv",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_19644",
        "compensated_uv == 19644",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TC: 20644 - 1000 = 19644μV compensated EMF");
}

#[test]
fn type_k_range() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c_offset", "min_offset", "max_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Type K: -200°C to +1372°C. Use offset +500 → range [300, 1872]
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c_offset == 1000")); // 500°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_offset == 300")); // -200°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_offset == 1872")); // +1372°C
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_c_offset >= min_offset && temp_c_offset <= max_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TC: 500°C in Type K range [-200, +1372] → in range",
    );
}

#[test]
fn adc_resolution_bits() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_bits", u32_ty());
    ctx.declare_var_typed("max_code", u32_ty());
    // 14-bit ADC: max code = 2^14 - 1 = 16383. Precompute.
    ctx.push_obligation(ProofObligation::assume("rb", "resolution_bits == 14"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_code == 16383")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_16383", "max_code == 16383"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TC: 14-bit ADC → max code 16383 (precomputed)");
}

#[test]
fn open_circuit_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_reading", "open_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("open_circuit", i32_ty());
    // Open thermocouple: ADC saturates high
    ctx.push_obligation(ProofObligation::assume("ar", "adc_reading == 16300"));
    ctx.push_obligation(ProofObligation::assume("ot", "open_threshold == 16000"));
    ctx.push_obligation(ProofObligation::assume(
        "oc_def",
        "open_circuit == if adc_reading >= open_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "open_circuit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TC: ADC 16300 ≥ 16000 threshold → open circuit detected",
    );
}

#[test]
fn averaging_filter() {
    let mut ctx = VerificationContext::new();
    for v in &["sample_sum", "sample_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("average", u32_ty());
    // Average of 4 samples. Precompute: 40000/4 = 10000
    ctx.push_obligation(ProofObligation::assume("ss", "sample_sum == 40000"));
    ctx.push_obligation(ProofObligation::assume("sc", "sample_count == 4"));
    ctx.push_obligation(ProofObligation::assume("avg", "average == 10000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_10000", "average == 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TC: average(40000, 4 samples) = 10000 (precomputed)",
    );
}

#[test]
fn alarm_high_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_reading", "alarm_high"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("alarm_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tr", "temp_reading == 850")); // 85.0°C
    ctx.push_obligation(ProofObligation::assume("ah", "alarm_high == 800")); // 80.0°C
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "alarm_active == if temp_reading > alarm_high { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "alarm_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TC: 85.0°C > 80.0°C alarm threshold → alarm active",
    );
}

#[test]
fn linearization_segment() {
    let mut ctx = VerificationContext::new();
    for v in &["emf_uv", "segment_start_uv", "segment_end_uv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_segment", i32_ty());
    // Piecewise linearization: find which segment contains the EMF value
    ctx.push_obligation(ProofObligation::assume("eu", "emf_uv == 12000"));
    ctx.push_obligation(ProofObligation::assume("ss", "segment_start_uv == 10000"));
    ctx.push_obligation(ProofObligation::assume("se", "segment_end_uv == 15000"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "in_segment == if emf_uv >= segment_start_uv && emf_uv <= segment_end_uv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_segment == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TC: 12000μV in [10000, 15000] → in linearization segment",
    );
}

#[test]
fn noise_rejection() {
    let mut ctx = VerificationContext::new();
    for v in &["sample_delta", "noise_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_noise", i32_ty());
    // Reject sample-to-sample changes exceeding physical possibility
    ctx.push_obligation(ProofObligation::assume("sd", "sample_delta == 500"));
    ctx.push_obligation(ProofObligation::assume("nt", "noise_threshold == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "in_def",
        "is_noise == if sample_delta > noise_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_noise == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TC: delta 500 > 100 threshold → noise spike rejected",
    );
}

#[test]
fn conversion_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["conversions_per_sec", "required_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Typical: 10-100 conversions/sec
    ctx.push_obligation(ProofObligation::assume("cs", "conversions_per_sec == 50"));
    ctx.push_obligation(ProofObligation::assume("rr", "required_rate == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if conversions_per_sec >= required_rate { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TC: 50 conv/s ≥ 10 required → rate OK");
}

#[test]
fn differential_input() {
    let mut ctx = VerificationContext::new();
    for v in &["positive_uv", "negative_uv", "differential_uv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Differential voltage = V+ - V-
    ctx.push_obligation(ProofObligation::assume("pv", "positive_uv == 15000"));
    ctx.push_obligation(ProofObligation::assume("nv", "negative_uv == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "du_def",
        "differential_uv == positive_uv - negative_uv",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_12000",
        "differential_uv == 12000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TC: 15000 - 3000 = 12000μV differential");
}
