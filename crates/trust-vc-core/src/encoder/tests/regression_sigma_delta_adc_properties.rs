// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn oversampling_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["osr", "min_osr", "max_osr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("osr_ok", i32_ty());
    // Oversampling ratio: typically 32-2048
    ctx.push_obligation(ProofObligation::assume("o", "osr == 256"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_osr == 32"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_osr == 2048"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "osr_ok == if osr >= min_osr && osr <= max_osr { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "osr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ΣΔ ADC: OSR 256 in [32, 2048] → OK");
}

#[test]
fn resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["bits", "min_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // ΣΔ ADC: high resolution (16-32 bits typical)
    ctx.push_obligation(ProofObligation::assume("b", "bits == 24"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bits == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if bits >= min_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ΣΔ ADC: 24-bit ≥ 16-bit min → resolution OK");
}

#[test]
fn modulator_order() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("order", u32_ty());
    ctx.declare_var_typed("valid_order", i32_ty());
    // ΣΔ modulator orders: 1, 2, 3 (higher order = more aggressive noise shaping)
    ctx.push_obligation(ProofObligation::assume("o", "order == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_order == if order >= 1 && order <= 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_order == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ΣΔ ADC: order 2 in [1, 3] → valid modulator");
}

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["data_rate_sps", "min_sps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Output data rate (SPS): inversely proportional to OSR
    ctx.push_obligation(ProofObligation::assume("dr", "data_rate_sps == 1000"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_sps == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if data_rate_sps >= min_sps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ΣΔ ADC: 1000 SPS ≥ 10 SPS min → rate OK");
}

#[test]
fn input_channel() {
    let mut ctx = VerificationContext::new();
    for v in &["channel", "max_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ch_valid", i32_ty());
    // Multiplexed input channels (e.g., ADS1256: 8 single-ended / 4 differential)
    ctx.push_obligation(ProofObligation::assume("c", "channel == 3"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_channels == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "cv_def",
        "ch_valid == if channel <= max_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ch_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ΣΔ ADC: channel 3 ≤ 7 max → valid");
}

#[test]
fn pga_gain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gain", u32_ty());
    ctx.declare_var_typed("gain_valid", i32_ty());
    // Programmable Gain Amplifier: 1, 2, 4, 8, 16, 32, 64
    ctx.push_obligation(ProofObligation::assume("g", "gain == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "gv_def",
        "gain_valid == if gain == 1 || gain == 2 || gain == 4 || gain == 8 || gain == 16 || gain == 32 || gain == 64 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "gain_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ΣΔ ADC: PGA gain 16 is a valid setting");
}

#[test]
fn noise_free_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["noise_free", "min_noise_free"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("nf_ok", i32_ty());
    // Noise-free resolution: typically 2-4 bits less than nominal
    ctx.push_obligation(ProofObligation::assume("nf", "noise_free == 20"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_noise_free == 18"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "nf_ok == if noise_free >= min_noise_free { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "nf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ΣΔ ADC: 20 noise-free bits ≥ 18 min → OK");
}

#[test]
fn chop_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chop_enabled", u32_ty());
    ctx.declare_var_typed("offset_cancelled", i32_ty());
    // Chopper mode: cancels offset and 1/f noise
    ctx.push_obligation(ProofObligation::assume("ce", "chop_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "oc_def",
        "offset_cancelled == if chop_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "offset_cancelled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ΣΔ ADC: chop=1 → offset cancelled");
}

#[test]
fn reference_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vref_mv", "min_vref_mv", "max_vref_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ref_ok", i32_ty());
    // External reference voltage range
    ctx.push_obligation(ProofObligation::assume("vm", "vref_mv == 2500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vref_mv == 500"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vref_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ref_ok == if vref_mv >= min_vref_mv && vref_mv <= max_vref_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ref_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ΣΔ ADC: Vref 2.5V in [0.5, 5.0] → reference OK");
}

#[test]
fn digital_filter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("filter_type", u32_ty());
    ctx.declare_var_typed("is_sinc3", i32_ty());
    // Digital filter types: 0=sinc1, 1=sinc2, 2=sinc3, 3=sinc4, 4=FIR
    ctx.push_obligation(ProofObligation::assume("ft", "filter_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_sinc3 == if filter_type == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_sinc3 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ΣΔ ADC: filter_type=2 → sinc3 filter");
}
