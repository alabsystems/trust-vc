// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn temperature_range_low() {
    let mut ctx = VerificationContext::new();
    for v in &["temp", "range_min", "range_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Offset +500: value 460 means -40C, range 200 (-300C) to 500 (0C)
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 460"));
    ctx.push_obligation(ProofObligation::assume("range_min_val", "range_min == 200"));
    ctx.push_obligation(ProofObligation::assume("range_max_val", "range_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "temp >= range_min && temp <= range_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "low pyrometer temp 460 (-40C) in range [200,500]");
}

#[test]
fn temperature_range_high() {
    let mut ctx = VerificationContext::new();
    for v in &["temp", "range_min", "range_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Offset +500: value 3500 means 3000C, range 1000 (500C) to 4000 (3500C)
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 3500"));
    ctx.push_obligation(ProofObligation::assume(
        "range_min_val",
        "range_min == 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "range_max_val",
        "range_max == 4000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "temp >= range_min && temp <= range_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "high pyrometer temp 3500 (3000C) in range [1000,4000]",
    );
}

#[test]
fn spectral_response() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("band", u32_ty());
    ctx.declare_var_typed("valid_band", i32_ty());
    // 1=broadband (8-14um), 2=mid-wave (3-5um), 3=short-wave (1-2.5um), 4=ratio/two-color
    ctx.push_obligation(ProofObligation::assume("band_val", "band == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_band_def",
        "valid_band == if band == 1 || band == 2 || band == 3 || band == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_band == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectral band 1 (broadband 8-14um) is valid");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy", "max_accuracy"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("accuracy_ok", i32_ty());
    // Accuracy x10: value 10 means 1.0C, max 30 means 3.0C
    ctx.push_obligation(ProofObligation::assume("accuracy_val", "accuracy == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "max_accuracy_val",
        "max_accuracy == 30",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_ok_def",
        "accuracy_ok == if accuracy <= max_accuracy { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("within_spec", "accuracy_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 10 (1.0C) within max 30 (3.0C)");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["t90", "t90_min", "t90_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // T90 response time in ms
    ctx.push_obligation(ProofObligation::assume("t90_val", "t90 == 10"));
    ctx.push_obligation(ProofObligation::assume("t90_min_val", "t90_min == 1"));
    ctx.push_obligation(ProofObligation::assume("t90_max_val", "t90_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "t90 >= t90_min && t90 <= t90_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "T90 response 10ms in range [1,5000]ms");
}

#[test]
fn optical_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["dts_ratio", "dts_min", "dts_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Distance-to-spot ratio: value 100 means 100:1, range 10:1 to 300:1
    ctx.push_obligation(ProofObligation::assume("dts_val", "dts_ratio == 100"));
    ctx.push_obligation(ProofObligation::assume("dts_min_val", "dts_min == 10"));
    ctx.push_obligation(ProofObligation::assume("dts_max_val", "dts_max == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "dts_ratio >= dts_min && dts_ratio <= dts_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "optical resolution 100:1 in range [10:1,300:1]");
}

#[test]
fn emissivity_adjustable() {
    let mut ctx = VerificationContext::new();
    for v in &["emissivity", "emiss_min", "emiss_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Emissivity x100: value 95 means 0.95, range 10 (0.10) to 100 (1.00)
    ctx.push_obligation(ProofObligation::assume(
        "emissivity_val",
        "emissivity == 95",
    ));
    ctx.push_obligation(ProofObligation::assume("emiss_min_val", "emiss_min == 10"));
    ctx.push_obligation(ProofObligation::assume("emiss_max_val", "emiss_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "emissivity >= emiss_min && emissivity <= emiss_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "emissivity 95 (0.95) in range [10,100] (0.10-1.00)",
    );
}

#[test]
fn ambient_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["ambient", "amb_min", "amb_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Offset +500: value 520 means 20C, min 500 (0C), max 570 (70C)
    ctx.push_obligation(ProofObligation::assume("ambient_val", "ambient == 520"));
    ctx.push_obligation(ProofObligation::assume("amb_min_val", "amb_min == 500"));
    ctx.push_obligation(ProofObligation::assume("amb_max_val", "amb_max == 570"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "ambient >= amb_min && ambient <= amb_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ambient temp 520 (20C) in operating range [500,570] (0-70C)",
    );
}

#[test]
fn output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // 1=4-20mA, 2=0-10V, 3=thermocouple J, 4=thermocouple K, 5=RS485
    ctx.push_obligation(ProofObligation::assume("output_val", "output == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_output_def",
        "valid_output == if output == 1 || output == 2 || output == 3 || output == 4 || output == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type 5 (RS485) is valid");
}

#[test]
fn spot_diameter() {
    let mut ctx = VerificationContext::new();
    for v in &["spot_mm", "spot_min", "spot_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Measurement spot diameter in mm at 1m distance
    ctx.push_obligation(ProofObligation::assume("spot_val", "spot_mm == 10"));
    ctx.push_obligation(ProofObligation::assume("spot_min_val", "spot_min == 1"));
    ctx.push_obligation(ProofObligation::assume("spot_max_val", "spot_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "spot_mm >= spot_min && spot_mm <= spot_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spot diameter 10mm in range [1,100]mm at 1m");
}
