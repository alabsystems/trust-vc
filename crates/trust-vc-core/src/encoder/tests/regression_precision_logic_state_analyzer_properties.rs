// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Precision logic state analyzer property verification tests.

use super::*;

#[test]
fn test_channel_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channels >= 8 && channels <= 256",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "channels == 136"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "channels >= 8 && channels <= 256",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channel count must be within 8-256");
}

#[test]
fn test_state_clock_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("clock_mhz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "clock_mhz >= 1 && clock_mhz <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "clock_mhz == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "clock_mhz >= 1 && clock_mhz <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "state clock rate in MHz must be within 1-10000");
}

#[test]
fn test_timing_resolution_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "res_x100 > 0 && res_x100 < 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "res_x100 == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "res_x100 > 0 && res_x100 < 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "timing resolution (250 scaled x100 ps = 2.50 ns) within valid range",
    );
}

#[test]
fn test_memory_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "depth >= 1000 && depth <= 100000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "depth == 16000000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "depth >= 1000 && depth <= 100000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "memory depth in samples must be within 1000-100000000",
    );
}

#[test]
fn test_threshold_voltage_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thresh_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "thresh_x1000 > 0 && thresh_x1000 < 10000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "thresh_x1000 == 1800000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "thresh_x1000 > 0 && thresh_x1000 < 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "threshold voltage (1800000 scaled x1000 mV = 1800.000 mV) within valid range",
    );
}

#[test]
fn test_trigger_levels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("levels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "levels >= 1 && levels <= 16",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "levels == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "levels >= 1 && levels <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of trigger levels must be within 1-16");
}

#[test]
fn test_protocol_decode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("proto", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "proto == 1 || proto == 2 || proto == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "proto == 1 || proto == 2 || proto == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protocol decode must be SPI(1), I2C(2), or UART(3)",
    );
}

#[test]
fn test_acquisition_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "acq == 1 || acq == 2 || acq == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "acq == 1 || acq == 2 || acq == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "acquisition mode must be state(1), timing(2), or mixed(3)",
    );
}

#[test]
fn test_trigger_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trig", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "trig == 1 || trig == 2 || trig == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "trig == 1 || trig == 2 || trig == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trigger type must be pattern(1), sequence(2), or edge(3)",
    );
}

#[test]
fn test_automatic_setup_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("enabled", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "auto_setup",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic setup flag enabled implies conditional evaluates to 1",
    );
}
