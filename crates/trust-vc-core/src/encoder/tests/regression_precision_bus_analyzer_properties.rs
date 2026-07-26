// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Regression tests: precision bus analyzer properties
// Formal verification of digital communication bus protocol analyzer parameters
// (PCIe, USB, I2C, SPI, CAN serial/parallel bus debugging)

use super::*;

#[test]
fn test_bus_analyzer_max_data_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "rate >= 1 && rate <= 40000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rate_bounded",
        "rate >= 1 && rate <= 40000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "maximum data rate must be between 1 and 40000 Mbps",
    );
}

#[test]
fn test_bus_analyzer_channel_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "channel_range",
        "channels >= 1 && channels <= 64",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "channel_bounded",
        "channels > 0 && channels <= 64",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of channels must be between 1 and 64");
}

#[test]
fn test_bus_analyzer_capture_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "depth_range",
        "depth >= 1 && depth <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "depth_bounded",
        "depth > 0 && depth <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capture depth must be between 1 and 1000000 frames",
    );
}

#[test]
fn test_bus_analyzer_timing_resolution_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res_x1000 >= 1 && res_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_bounded",
        "res_x1000 >= 1 && res_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "timing resolution x1000 must be between 1 and 10000 representing 0.001-10.000 ns",
    );
}

#[test]
fn test_bus_analyzer_trigger_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trig_depth", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "trig_range",
        "trig_depth >= 1 && trig_depth <= 256",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "trig_bounded",
        "trig_depth > 0 && trig_depth <= 256",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trigger depth must be between 1 and 256 levels");
}

#[test]
fn test_bus_analyzer_protocol_decode_layers_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("layers", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "layers_range",
        "layers >= 1 && layers <= 7",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "layers_bounded",
        "layers > 0 && layers <= 7",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "protocol decode layers must be between 1 and 7");
}

#[test]
fn test_bus_analyzer_bus_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bus_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bus_type_valid",
        "bus_type == 1 || bus_type == 2 || bus_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bus_type_is_known",
        "bus_type == 1 || bus_type == 2 || bus_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bus type must be serial(1), parallel(2), or mixed(3)",
    );
}

#[test]
fn test_bus_analyzer_trigger_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trig_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "trig_mode_valid",
        "trig_mode == 1 || trig_mode == 2 || trig_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "trig_mode_is_known",
        "trig_mode == 1 || trig_mode == 2 || trig_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trigger mode must be edge(1), pattern(2), or state(3)",
    );
}

#[test]
fn test_bus_analyzer_analysis_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analysis_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "analysis_mode_valid",
        "analysis_mode == 1 || analysis_mode == 2 || analysis_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "analysis_mode_is_known",
        "analysis_mode == 1 || analysis_mode == 2 || analysis_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analysis mode must be realtime(1), post-capture(2), or streaming(3)",
    );
}

#[test]
fn test_bus_analyzer_auto_protocol_detection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_detect", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_detect_boolean",
        "auto_detect == 0 || auto_detect == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_detect_is_flag",
        "auto_detect >= 0 && auto_detect <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic protocol detection flag must be 0 (off) or 1 (on)",
    );
}
