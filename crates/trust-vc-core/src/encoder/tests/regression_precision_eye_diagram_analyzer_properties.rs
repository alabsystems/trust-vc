// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Regression tests: precision eye diagram analyzer property verification

use super::*;

#[test]
fn test_eye_diagram_analyzer_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bandwidth_mhz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "bandwidth_mhz >= 1 && bandwidth_mhz <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "bandwidth_mhz == 33000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "bandwidth_mhz >= 1 && bandwidth_mhz <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bandwidth 33000 MHz within 1-100000 MHz range");
}

#[test]
fn test_eye_diagram_analyzer_data_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("data_rate_mbps", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "data_rate_mbps >= 1 && data_rate_mbps <= 400000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "data_rate_mbps == 112000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "data_rate_mbps >= 1 && data_rate_mbps <= 400000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "data rate 112000 Mbps within 1-400000 Mbps range");
}

#[test]
fn test_eye_diagram_analyzer_vertical_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_bits", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "resolution_bits >= 8 && resolution_bits <= 16",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "resolution_bits == 12"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "resolution_bits >= 8 && resolution_bits <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vertical resolution 12 bits within 8-16 bits range",
    );
}

#[test]
fn test_eye_diagram_analyzer_eye_height_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("height_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "height_x1000 > 0 && height_x1000 < 2000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "height_x1000 == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "height_x1000 > 0 && height_x1000 < 2000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "eye height x1000 mV value 50000 (meaning 50.000 mV) within valid range",
    );
}

#[test]
fn test_eye_diagram_analyzer_eye_width_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "width_x100 > 0 && width_x100 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "width_x100 == 3500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "width_x100 > 0 && width_x100 < 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "eye width x100 ps value 3500 (meaning 35.00 ps) within valid range",
    );
}

#[test]
fn test_eye_diagram_analyzer_number_of_samples_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("samples", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "samples >= 1000 && samples <= 100000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "samples == 10000000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "samples >= 1000 && samples <= 100000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "number of samples 10000000 within 1000-100000000 range",
    );
}

#[test]
fn test_eye_diagram_analyzer_signal_standard_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("std", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "std == 1 || std == 2 || std == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "std == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "std == 1 || std == 2 || std == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "signal standard is NRZ(1), PAM4(2), or PAM8(3)");
}

#[test]
fn test_eye_diagram_analyzer_equalization_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "eq == 1 || eq == 2 || eq == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "eq == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "eq == 1 || eq == 2 || eq == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "equalization type is CTLE(1), DFE(2), or FFE(3)");
}

#[test]
fn test_eye_diagram_analyzer_trigger_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trig", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "trig == 1 || trig == 2 || trig == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "trig == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "trig == 1 || trig == 2 || trig == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trigger method is clock-recovery(1), pattern-lock(2), or external(3)",
    );
}

#[test]
fn test_eye_diagram_analyzer_automatic_mask_margin_testing_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_set", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mask_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic mask margin testing flag set implies conditional evaluates to 1",
    );
}
