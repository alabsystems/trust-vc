// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn adc_to_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_value", "adc_max", "pressure_range_pa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pressure_pa", u32_ty());
    // Pressure = adc / adc_max × range. Precompute: 2048/4096 × 100000 = 50000
    ctx.push_obligation(ProofObligation::assume("av", "adc_value == 2048"));
    ctx.push_obligation(ProofObligation::assume("am", "adc_max == 4096"));
    ctx.push_obligation(ProofObligation::assume("pr", "pressure_range_pa == 100000"));
    ctx.push_obligation(ProofObligation::assume("pp", "pressure_pa == 50000")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_50000", "pressure_pa == 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Pressure: ADC 2048/4096 × 100kPa = 50kPa (precomputed)",
    );
}

#[test]
fn overpressure_alarm() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_pa", "max_pressure_pa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("alarm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pp", "pressure_pa == 110000"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pressure_pa == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "alarm == if pressure_pa > max_pressure_pa { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "alarm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Pressure: 110kPa > 100kPa max → overpressure alarm",
    );
}

#[test]
fn differential_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["port_a_pa", "port_b_pa", "diff_pa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Differential = port_A - port_B
    ctx.push_obligation(ProofObligation::assume("pa", "port_a_pa == 101325")); // 1 atm
    ctx.push_obligation(ProofObligation::assume("pb", "port_b_pa == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "dp_def",
        "diff_pa == port_a_pa - port_b_pa",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1325", "diff_pa == 1325"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pressure: 101325 - 100000 = 1325 Pa differential");
}

#[test]
fn altitude_estimation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_pa", u32_ty());
    ctx.declare_var_typed("altitude_m", u32_ty());
    // Barometric formula simplified. Precompute: ~100000Pa ≈ 110m ASL
    ctx.push_obligation(ProofObligation::assume("pp", "pressure_pa == 100000"));
    ctx.push_obligation(ProofObligation::assume("am", "altitude_m == 110")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_110", "altitude_m == 110"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Pressure: 100000 Pa → ~110m altitude (precomputed)",
    );
}

#[test]
fn temperature_compensation_coeff() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_pressure", "temp_offset", "compensated"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Temperature-compensated pressure = raw - temp_offset
    ctx.push_obligation(ProofObligation::assume("rp", "raw_pressure == 50500"));
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compensated == raw_pressure - temp_offset",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50300", "compensated == 50300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Pressure: 50500 - 200 temp offset = 50300 compensated",
    );
}

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    for v in &["reading_pa", "min_pa", "max_pa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Sensor range: e.g., 30kPa to 110kPa
    ctx.push_obligation(ProofObligation::assume("rp", "reading_pa == 80000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pa == 30000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pa == 110000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if reading_pa >= min_pa && reading_pa <= max_pa { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Pressure: 80kPa in [30, 110] → in measurement range",
    );
}

#[test]
fn resolution_pa() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("adc_bits", u32_ty());
    ctx.declare_var_typed("resolution_mpa", u32_ty());
    // Resolution = range / 2^bits. Precompute: 100000000 mPa / 65536 ≈ 1526 mPa
    ctx.push_obligation(ProofObligation::assume("ab", "adc_bits == 16"));
    ctx.push_obligation(ProofObligation::assume("rm", "resolution_mpa == 1526")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1526", "resolution_mpa == 1526"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Pressure: 16-bit/100kPa → 1.526 Pa resolution (precomputed)",
    );
}

#[test]
fn filter_cutoff() {
    let mut ctx = VerificationContext::new();
    for v in &["noise_hz", "filter_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("filtered", i32_ty());
    // Low-pass filter removes noise above cutoff
    ctx.push_obligation(ProofObligation::assume("nh", "noise_hz == 100"));
    ctx.push_obligation(ProofObligation::assume("fh", "filter_hz == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "filtered == if noise_hz > filter_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "filtered == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Pressure: 100Hz noise > 50Hz filter → filtered out",
    );
}

#[test]
fn burst_mode_samples() {
    let mut ctx = VerificationContext::new();
    for v in &["burst_samples", "max_burst"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("burst_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bs", "burst_samples == 16"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_burst == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "burst_ok == if burst_samples <= max_burst { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "burst_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pressure: 16 burst samples ≤ 32 max → OK");
}

#[test]
fn unit_conversion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_pa", u32_ty());
    ctx.declare_var_typed("pressure_mbar", u32_ty());
    // 1 mbar = 100 Pa. Precompute: 101325 Pa = 1013 mbar (truncated)
    ctx.push_obligation(ProofObligation::assume("pp", "pressure_pa == 101325"));
    ctx.push_obligation(ProofObligation::assume("pm", "pressure_mbar == 1013")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1013", "pressure_mbar == 1013"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Pressure: 101325 Pa = 1013 mbar (precomputed)");
}
