// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Precision digital oscilloscope property verification tests.

use super::*;

#[test]
fn test_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bandwidth_mhz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "bandwidth_mhz >= 50 && bandwidth_mhz <= 33000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "bandwidth_mhz == 8000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "bandwidth_mhz >= 50 && bandwidth_mhz <= 33000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bandwidth in MHz must be within 50-33000");
}

#[test]
fn test_sample_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_rate_gsps", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sample_rate_gsps >= 1 && sample_rate_gsps <= 256",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "sample_rate_gsps == 40"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sample_rate_gsps >= 1 && sample_rate_gsps <= 256",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample rate in GSa/s must be within 1-256");
}

#[test]
fn test_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channels >= 2 && channels <= 8",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "channels == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "channels >= 2 && channels <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "analog input channels must be within 2-8");
}

#[test]
fn test_memory_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("memory_depth_msa", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "memory_depth_msa >= 1 && memory_depth_msa <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "memory_depth_msa == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "memory_depth_msa >= 1 && memory_depth_msa <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "memory depth in megasamples must be within 1-100000",
    );
}

#[test]
fn test_vertical_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vertical_resolution_bits", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "vertical_resolution_bits >= 8 && vertical_resolution_bits <= 16",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "vertical_resolution_bits == 12",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "vertical_resolution_bits >= 8 && vertical_resolution_bits <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vertical resolution in bits must be within 8-16");
}

#[test]
fn test_input_impedance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("input_impedance_ohms", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "input_impedance_ohms >= 50 && input_impedance_ohms <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "input_impedance_ohms == 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "input_impedance_ohms >= 50 && input_impedance_ohms <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input impedance in ohms must be within 50-1000000");
}

#[test]
fn test_acquisition_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acq_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "acq_mode == 1 || acq_mode == 2 || acq_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "acq_mode == 1 || acq_mode == 2 || acq_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "acquisition mode must be sample(1), peak-detect(2), or average(3)",
    );
}

#[test]
fn test_trigger_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trigger_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "trigger_type == 1 || trigger_type == 2 || trigger_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "trigger_type == 1 || trigger_type == 2 || trigger_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trigger type must be edge(1), pulse(2), or pattern(3)",
    );
}

#[test]
fn test_probe_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "probe_type == 1 || probe_type == 2 || probe_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "probe_type == 1 || probe_type == 2 || probe_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "probe type must be passive(1), active(2), or differential(3)",
    );
}

#[test]
fn test_segmented_memory_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("enabled", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "segmented",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "segmented memory flag enabled implies conditional evaluates to 1",
    );
}
