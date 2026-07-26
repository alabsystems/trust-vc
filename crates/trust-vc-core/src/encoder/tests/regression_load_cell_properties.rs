// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn weight_from_adc() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_value", "adc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("weight_grams", u32_ty());
    // Weight = adc/adc_max × full_scale. Precompute: 500000/1000000 × 5000 = 2500g
    ctx.push_obligation(ProofObligation::assume("av", "adc_value == 500000"));
    ctx.push_obligation(ProofObligation::assume("am", "adc_max == 1000000"));
    ctx.push_obligation(ProofObligation::assume("wg", "weight_grams == 2500")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_2500", "weight_grams == 2500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Load cell: ADC 500K/1M → 2500g (precomputed)");
}

#[test]
fn overload_protection() {
    let mut ctx = VerificationContext::new();
    for v in &["weight_grams", "rated_capacity_grams"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("overloaded", i32_ty());
    // Overload when exceeding rated capacity
    ctx.push_obligation(ProofObligation::assume("wg", "weight_grams == 6000"));
    ctx.push_obligation(ProofObligation::assume(
        "rc",
        "rated_capacity_grams == 5000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "overloaded == if weight_grams > rated_capacity_grams { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "overloaded == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Load cell: 6000g > 5000g rated → overloaded");
}

#[test]
fn excitation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["excitation_mv", "rated_excitation_mv", "tolerance_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("excitation_ok", i32_ty());
    // Wheatstone bridge excitation: typically 5V or 10V ± tolerance
    ctx.push_obligation(ProofObligation::assume("em", "excitation_mv == 4980"));
    ctx.push_obligation(ProofObligation::assume("re", "rated_excitation_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("tm", "tolerance_mv == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "excitation_ok == if excitation_mv >= rated_excitation_mv - tolerance_mv && excitation_mv <= rated_excitation_mv + tolerance_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "excitation_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Load cell: 4980mV in [4950, 5050] → excitation OK");
}

#[test]
fn sensitivity_check() {
    let mut ctx = VerificationContext::new();
    for v in &["output_mv_per_v", "min_sensitivity", "max_sensitivity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sensitivity_ok", i32_ty());
    // Typical sensitivity: 2 mV/V ± 0.1 mV/V. Use ×100 scale: 200 ± 10
    ctx.push_obligation(ProofObligation::assume("om", "output_mv_per_v == 198")); // 1.98 mV/V × 100
    ctx.push_obligation(ProofObligation::assume("mn", "min_sensitivity == 190")); // 1.90
    ctx.push_obligation(ProofObligation::assume("mx", "max_sensitivity == 210")); // 2.10
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sensitivity_ok == if output_mv_per_v >= min_sensitivity && output_mv_per_v <= max_sensitivity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sensitivity_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Load cell: 1.98 mV/V in [1.90, 2.10] → sensitivity OK",
    );
}

#[test]
fn zero_balance() {
    let mut ctx = VerificationContext::new();
    for v in &["zero_offset_uv", "max_offset_uv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("zero_ok", i32_ty());
    // Zero balance (no load output): typically ±1% of full scale
    ctx.push_obligation(ProofObligation::assume("zo", "zero_offset_uv == 50"));
    ctx.push_obligation(ProofObligation::assume("mo", "max_offset_uv == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "zo_def",
        "zero_ok == if zero_offset_uv <= max_offset_uv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "zero_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Load cell: 50μV offset ≤ 100μV max → zero balance OK",
    );
}

#[test]
fn tare_subtraction() {
    let mut ctx = VerificationContext::new();
    for v in &["gross_weight", "tare_weight", "net_weight"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Net weight = gross - tare
    ctx.push_obligation(ProofObligation::assume("gw", "gross_weight == 3500"));
    ctx.push_obligation(ProofObligation::assume("tw", "tare_weight == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "nw_def",
        "net_weight == gross_weight - tare_weight",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3000", "net_weight == 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Load cell: 3500g gross - 500g tare = 3000g net");
}

#[test]
fn adc_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_bits", "min_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resolution_ok", i32_ty());
    // HX711: 24-bit ADC. Minimum for precision weighing: 16 bits
    ctx.push_obligation(ProofObligation::assume("ab", "adc_bits == 24"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bits == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resolution_ok == if adc_bits >= min_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resolution_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Load cell: 24-bit ADC ≥ 16-bit min → resolution OK",
    );
}

#[test]
fn creep_error() {
    let mut ctx = VerificationContext::new();
    for v in &["initial_reading", "reading_after_30min", "max_creep"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("creep_ok", i32_ty());
    // Creep: output change under constant load over time
    ctx.push_obligation(ProofObligation::assume("ir", "initial_reading == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "ra",
        "reading_after_30min == 10003",
    ));
    ctx.push_obligation(ProofObligation::assume("mc", "max_creep == 10"));
    // Creep = |after - initial|
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "creep_ok == if reading_after_30min - initial_reading <= max_creep { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "creep_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Load cell: creep 3 counts ≤ 10 max → creep OK");
}

#[test]
fn sample_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_hz", "min_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // HX711: 10 or 80 SPS
    ctx.push_obligation(ProofObligation::assume("rh", "rate_hz == 80"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_rate_hz == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if rate_hz >= min_rate_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Load cell: 80 SPS ≥ 10 SPS min → rate OK");
}

#[test]
fn gain_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gain", u32_ty());
    ctx.declare_var_typed("is_high_gain", i32_ty());
    // HX711: gain 32, 64, or 128
    ctx.push_obligation(ProofObligation::assume("g", "gain == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "ih_def",
        "is_high_gain == if gain == 128 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_high_gain == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Load cell: gain=128 → high gain mode");
}
