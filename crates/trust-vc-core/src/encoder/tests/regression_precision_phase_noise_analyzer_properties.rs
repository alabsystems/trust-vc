// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Regression tests: precision phase noise analyzer property verification

use super::*;

#[test]
fn test_carrier_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("carrier_ghz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "carrier_ghz >= 1 && carrier_ghz <= 67",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "carrier_ghz == 26"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "carrier_ghz >= 1 && carrier_ghz <= 67",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "carrier frequency 26 GHz within 1-67 GHz range");
}

#[test]
fn test_offset_frequency_range_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("offset_mhz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "offset_mhz >= 1 && offset_mhz <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "offset_mhz == 40"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "offset_mhz >= 1 && offset_mhz <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "offset frequency 40 MHz within 1-100 MHz range");
}

#[test]
fn test_noise_floor_offset200_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise_floor_off200", u32_ty());
    // dBc/Hz with offset +200: -180 dBc/Hz -> 20, -100 dBc/Hz -> 100
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "noise_floor_off200 >= 20 && noise_floor_off200 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "noise_floor_off200 == 25"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "noise_floor_off200 >= 20 && noise_floor_off200 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "noise floor offset+200 value 25 (meaning -175 dBc/Hz) within 20-100 range",
    );
}

#[test]
fn test_cross_correlation_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("xcorr_ch", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "xcorr_ch >= 2 && xcorr_ch <= 8",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "xcorr_ch == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "xcorr_ch >= 2 && xcorr_ch <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cross-correlation channels 4 within 2-8 range");
}

#[test]
fn test_measurement_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    // Speed x10 seconds per decade: 1-1000 represents 0.1-100.0 s/decade
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "speed_x10 >= 1 && speed_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "speed_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "speed_x10 >= 1 && speed_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement speed x10 value 50 (meaning 5.0 s/decade) within 1-1000 range",
    );
}

#[test]
fn test_measurement_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    // 1=PLL, 2=cross-correlation, 3=delay-line-discriminator
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement method is PLL(1), cross-correlation(2), or delay-line-discriminator(3)",
    );
}

#[test]
fn test_spur_detection_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spur_mode", i32_ty());
    // 1=auto, 2=manual, 3=AM-rejection
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "spur_mode == 1 || spur_mode == 2 || spur_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "spur_mode == 1 || spur_mode == 2 || spur_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spur detection mode is auto(1), manual(2), or AM-rejection(3)",
    );
}

#[test]
fn test_reference_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_src", i32_ty());
    // 1=internal-crystal, 2=external, 3=two-source
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "ref_src == 1 || ref_src == 2 || ref_src == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "ref_src == 1 || ref_src == 2 || ref_src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reference source is internal-crystal(1), external(2), or two-source(3)",
    );
}

#[test]
fn test_dynamic_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dyn_range_db", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "dyn_range_db >= 50 && dyn_range_db <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "dyn_range_db == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "dyn_range_db >= 50 && dyn_range_db <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dynamic range 150 dB within 50-200 dB range");
}

#[test]
fn test_real_time_display_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_set", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "real-time display flag set implies conditional evaluates to 1",
    );
}
