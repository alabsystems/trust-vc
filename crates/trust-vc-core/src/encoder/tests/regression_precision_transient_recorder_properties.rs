// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Precision transient recorder property verification tests.

use super::*;

#[test]
fn test_transient_recorder_sample_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_rate_mhz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sample_rate_mhz >= 1 && sample_rate_mhz <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "sample_rate_mhz == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sample_rate_mhz >= 1 && sample_rate_mhz <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample rate in MHz must be within 1-100000");
}

#[test]
fn test_transient_recorder_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_bits", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "resolution_bits >= 8 && resolution_bits <= 16",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "resolution_bits == 14"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "resolution_bits >= 8 && resolution_bits <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution in bits must be within 8-16");
}

#[test]
fn test_transient_recorder_record_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("record_length_msa", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "record_length_msa >= 1 && record_length_msa <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "record_length_msa == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "record_length_msa >= 1 && record_length_msa <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "record length in Msamples must be within 1-10000");
}

#[test]
fn test_transient_recorder_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bandwidth_mhz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "bandwidth_mhz >= 1 && bandwidth_mhz <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "bandwidth_mhz == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "bandwidth_mhz >= 1 && bandwidth_mhz <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bandwidth in MHz must be within 1-50000");
}

#[test]
fn test_transient_recorder_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channels >= 1 && channels <= 64",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "channels == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "channels >= 1 && channels <= 64",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of channels must be within 1-64");
}

#[test]
fn test_transient_recorder_dynamic_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dynamic_range_db", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "dynamic_range_db >= 40 && dynamic_range_db <= 120",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "dynamic_range_db == 84"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "dynamic_range_db >= 40 && dynamic_range_db <= 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dynamic range in dB must be within 40-120");
}

#[test]
fn test_transient_recorder_trigger_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trigger_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "trigger_mode == 1 || trigger_mode == 2 || trigger_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "trigger_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "trigger_mode == 1 || trigger_mode == 2 || trigger_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trigger mode must be edge(1), level(2), or window(3)",
    );
}

#[test]
fn test_transient_recorder_memory_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("memory_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "memory_mode == 1 || memory_mode == 2 || memory_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "memory_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "memory_mode == 1 || memory_mode == 2 || memory_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "memory mode must be segmented(1), continuous(2), or circular(3)",
    );
}

#[test]
fn test_transient_recorder_interface_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("interface", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "interface == 1 || interface == 2 || interface == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "interface == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "interface == 1 || interface == 2 || interface == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "interface must be PCI(1), PXI(2), or USB(3)");
}

#[test]
fn test_transient_recorder_pre_trigger_capture_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("enabled", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "pre_trigger",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pre-trigger capture flag enabled implies conditional evaluates to 1",
    );
}
