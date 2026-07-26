// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn comparator_count() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution_bits", "comparators"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Flash ADC: 2^N - 1 comparators. Precompute: 2^8 - 1 = 255
    ctx.push_obligation(ProofObligation::assume("rb", "resolution_bits == 8"));
    ctx.push_obligation(ProofObligation::assume("c", "comparators == 255")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_255", "comparators == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flash ADC: 8-bit → 255 comparators (precomputed)");
}

#[test]
fn sampling_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["sample_rate_msps", "min_rate_msps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Flash ADC: extremely high sampling rates (>100 MSPS)
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate_msps == 500"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_rate_msps == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if sample_rate_msps >= min_rate_msps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flash ADC: 500 MSPS ≥ 100 MSPS min → rate OK");
}

#[test]
fn input_voltage_range() {
    let mut ctx = VerificationContext::new();
    for v in &["input_mv", "vref_low_mv", "vref_high_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Input must be within reference voltage range
    ctx.push_obligation(ProofObligation::assume("im", "input_mv == 1200"));
    ctx.push_obligation(ProofObligation::assume("vl", "vref_low_mv == 0"));
    ctx.push_obligation(ProofObligation::assume("vh", "vref_high_mv == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if input_mv >= vref_low_mv && input_mv <= vref_high_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flash ADC: 1.2V in [0, 2.0] → input in range");
}

#[test]
fn power_consumption() {
    let mut ctx = VerificationContext::new();
    for v in &["power_mw", "max_power_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_ok", i32_ty());
    // Flash ADCs consume significant power (scales with 2^N)
    ctx.push_obligation(ProofObligation::assume("pm", "power_mw == 800"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_mw == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "power_ok == if power_mw <= max_power_mw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flash ADC: 800mW ≤ 2000mW max → power OK");
}

#[test]
fn dnl_spec() {
    let mut ctx = VerificationContext::new();
    for v in &["dnl_x100", "max_dnl_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dnl_ok", i32_ty());
    // Differential nonlinearity: ±0.5 LSB typical → ×100 scale
    ctx.push_obligation(ProofObligation::assume("dn", "dnl_x100 == 30")); // 0.30 LSB
    ctx.push_obligation(ProofObligation::assume("md", "max_dnl_x100 == 100")); // 1.00 LSB
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dnl_ok == if dnl_x100 <= max_dnl_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dnl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flash ADC: DNL 0.30 LSB ≤ 1.00 LSB max → OK");
}

#[test]
fn inl_spec() {
    let mut ctx = VerificationContext::new();
    for v in &["inl_x100", "max_inl_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("inl_ok", i32_ty());
    // Integral nonlinearity: typically ±1 LSB for flash ADC
    ctx.push_obligation(ProofObligation::assume("in", "inl_x100 == 50")); // 0.50 LSB
    ctx.push_obligation(ProofObligation::assume("mi", "max_inl_x100 == 100")); // 1.00 LSB
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "inl_ok == if inl_x100 <= max_inl_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "inl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flash ADC: INL 0.50 LSB ≤ 1.00 LSB max → OK");
}

#[test]
fn effective_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["enob_x10", "min_enob_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("enob_ok", i32_ty());
    // ENOB (Effective Number Of Bits): typically 0.5-1 bit less than nominal
    ctx.push_obligation(ProofObligation::assume("en", "enob_x10 == 73")); // 7.3 ENOB
    ctx.push_obligation(ProofObligation::assume("me", "min_enob_x10 == 70")); // 7.0 min
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "enob_ok == if enob_x10 >= min_enob_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "enob_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flash ADC: 7.3 ENOB ≥ 7.0 min → effective bits OK");
}

#[test]
fn encoder_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("encoder", u32_ty());
    ctx.declare_var_typed("is_thermometer", i32_ty());
    // Output encoding: 0=binary, 1=thermometer, 2=Gray code
    ctx.push_obligation(ProofObligation::assume("e", "encoder == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "it_def",
        "is_thermometer == if encoder == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_thermometer == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flash ADC: encoder=1 → thermometer code output");
}

#[test]
fn aperture_jitter() {
    let mut ctx = VerificationContext::new();
    for v in &["jitter_ps", "max_jitter_ps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("jitter_ok", i32_ty());
    // Aperture jitter: critical at high sample rates (typically <1ps)
    ctx.push_obligation(ProofObligation::assume("jp", "jitter_ps == 500")); // 0.5ps
    ctx.push_obligation(ProofObligation::assume("mj", "max_jitter_ps == 1000")); // 1.0ps
    ctx.push_obligation(ProofObligation::assume(
        "jo_def",
        "jitter_ok == if jitter_ps <= max_jitter_ps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "jitter_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flash ADC: 0.5ps jitter ≤ 1.0ps max → OK");
}

#[test]
fn reference_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vref_mv", "target_vref_mv", "tolerance_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ref_ok", i32_ty());
    // Reference voltage accuracy
    ctx.push_obligation(ProofObligation::assume("vm", "vref_mv == 2002"));
    ctx.push_obligation(ProofObligation::assume("tv", "target_vref_mv == 2000"));
    ctx.push_obligation(ProofObligation::assume("tm", "tolerance_mv == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ref_ok == if vref_mv >= target_vref_mv - tolerance_mv && vref_mv <= target_vref_mv + tolerance_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ref_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flash ADC: Vref 2.002V in [1.990, 2.010] → OK");
}
