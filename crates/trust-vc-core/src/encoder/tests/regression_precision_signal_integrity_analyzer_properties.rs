// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Regression tests: precision signal integrity analyzer properties
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_signal_integrity_analyzer_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bw_mhz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bandwidth_range",
        "bw_mhz >= 1 && bw_mhz <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bandwidth_positive_and_bounded",
        "bw_mhz > 0 && bw_mhz <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bandwidth must be bounded between 1 and 100000 MHz",
    );
}

#[test]
fn test_signal_integrity_analyzer_rise_time_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rise_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rise_time_range",
        "rise_x1000 > 0 && rise_x1000 < 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rise_time_positive",
        "rise_x1000 >= 1 && rise_x1000 <= 999999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rise time scaled x1000 ps must be positive and within range",
    );
}

#[test]
fn test_signal_integrity_analyzer_jitter_measurement_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jit_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "jitter_range",
        "jit_x10000 > 0 && jit_x10000 < 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "jitter_positive",
        "jit_x10000 >= 1 && jit_x10000 <= 9999999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jitter measurement scaled x10000 ps must be positive and within range",
    );
}

#[test]
fn test_signal_integrity_analyzer_channel_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "channel_range",
        "num_channels >= 1 && num_channels <= 16",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "channel_bounded",
        "num_channels > 0 && num_channels <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "number of channels must be bounded between 1 and 16",
    );
}

#[test]
fn test_signal_integrity_analyzer_sample_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sample_rate_range",
        "sample_rate >= 1 && sample_rate <= 200000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sample_rate_positive_and_bounded",
        "sample_rate > 0 && sample_rate <= 200000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample rate must be bounded between 1 and 200000 MSa/s",
    );
}

#[test]
fn test_signal_integrity_analyzer_vertical_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vert_bits", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vert_range",
        "vert_bits >= 8 && vert_bits <= 16",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vert_bounded",
        "vert_bits >= 8 && vert_bits <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vertical resolution must be bounded between 8 and 16 bits",
    );
}

#[test]
fn test_signal_integrity_analyzer_sparam_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sparam", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sparam_valid",
        "sparam == 1 || sparam == 2 || sparam == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sparam_is_known_type",
        "sparam == 1 || sparam == 2 || sparam == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s-parameter type must be insertion-loss(1), return-loss(2), or crosstalk(3)",
    );
}

#[test]
fn test_signal_integrity_analyzer_deembedding_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("deembed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "deembed_valid",
        "deembed == 1 || deembed == 2 || deembed == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "deembed_is_known_method",
        "deembed == 1 || deembed == 2 || deembed == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "de-embedding method must be AFR(1), TDR(2), or peeling(3)",
    );
}

#[test]
fn test_signal_integrity_analyzer_compliance_standard_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("std_id", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "std_valid",
        "std_id == 1 || std_id == 2 || std_id == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "std_is_known",
        "std_id == 1 || std_id == 2 || std_id == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compliance standard must be PCIe(1), USB(2), or Ethernet(3)",
    );
}

#[test]
fn test_signal_integrity_analyzer_auto_equalization_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_eq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_eq_boolean",
        "auto_eq == 0 || auto_eq == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_eq_is_flag",
        "auto_eq >= 0 && auto_eq <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic equalization flag must be 0 (off) or 1 (on)",
    );
}
