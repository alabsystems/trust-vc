// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_digitizer_sample_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "rate >= 1 && rate <= 2000000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rate_bounded",
        "rate >= 1 && rate <= 2000000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample rate in [1, 2000000000]");
}

#[test]
fn test_digitizer_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bw_range",
        "bw >= 1 && bw <= 1000000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bw_bounded",
        "bw >= 1 && bw <= 1000000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "analog bandwidth in [1, 1000000000]");
}

#[test]
fn test_digitizer_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res >= 8 && res <= 16",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_bounded",
        "res >= 8 && res <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC resolution in [8, 16] bits");
}

#[test]
fn test_digitizer_memory_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mem", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mem_range",
        "mem >= 1000 && mem <= 100000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mem_bounded",
        "mem >= 1000 && mem <= 100000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "memory depth in [1000, 100000000] samples");
}

#[test]
fn test_digitizer_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ch", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ch_range", "ch >= 1 && ch <= 8"));
    ctx.push_obligation(ProofObligation::assert("ch_bounded", "ch >= 1 && ch <= 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input channels in [1, 8]");
}

#[test]
fn test_digitizer_input_range_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rng_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rng_range",
        "rng_x1000 >= 50 && rng_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rng_bounded",
        "rng_x1000 >= 50 && rng_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input range x1000 in [50, 10000]");
}

#[test]
fn test_digitizer_trigger_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trig", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "trig_vals",
        "trig == 1 || trig == 2 || trig == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "trig_bounded",
        "trig == 1 || trig == 2 || trig == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trigger type is edge, level, or pattern");
}

#[test]
fn test_digitizer_coupling_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cpl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cpl_vals",
        "cpl == 1 || cpl == 2 || cpl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cpl_bounded",
        "cpl == 1 || cpl == 2 || cpl == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "coupling is AC, DC, or GND");
}

#[test]
fn test_digitizer_data_format_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fmt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fmt_vals",
        "fmt == 1 || fmt == 2 || fmt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fmt_bounded",
        "fmt == 1 || fmt == 2 || fmt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "data format is binary, ASCII, or HDF5");
}

#[test]
fn test_digitizer_external_clock_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ext", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ext_vals", "ext == 0 || ext == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "ext_bounded",
        "ext == 0 || ext == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "external clock flag is 0 or 1");
}
