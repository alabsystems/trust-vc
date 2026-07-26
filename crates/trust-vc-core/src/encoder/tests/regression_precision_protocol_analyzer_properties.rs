// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Precision Protocol Analyzer property regression tests

use super::*;

#[test]
fn test_protocol_analyzer_data_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("data_rate_mbps", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "data_rate_mbps >= 1 && data_rate_mbps <= 400000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "data_rate_mbps == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "data_rate_mbps >= 1 && data_rate_mbps <= 400000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protocol analyzer data rate bounded 1-400000 Mbps with value 100000 Mbps",
    );
}

#[test]
fn test_protocol_analyzer_capture_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capture_depth", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "capture_depth >= 1000 && capture_depth <= 1000000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "capture_depth == 500000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "capture_depth >= 1000 && capture_depth <= 1000000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protocol analyzer capture depth bounded 1000-1000000000 frames with value 500000",
    );
}

#[test]
fn test_protocol_analyzer_timestamp_resolution_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ts_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "ts_x100 > 0 && ts_x100 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "ts_x100 == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "scaled",
        "ts_x100 * 100 > 0 && ts_x100 * 100 < 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protocol analyzer timestamp resolution x100 ns scaled bounded with value 100 (1 us)",
    );
}

#[test]
fn test_protocol_analyzer_number_of_ports_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_ports", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "num_ports >= 1 && num_ports <= 48",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "num_ports == 24"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "num_ports >= 1 && num_ports <= 48",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protocol analyzer number of ports bounded 1-48 with value 24",
    );
}

#[test]
fn test_protocol_analyzer_filter_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("filter_depth", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "filter_depth >= 1 && filter_depth <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "filter_depth == 256"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "filter_depth >= 1 && filter_depth <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protocol analyzer filter depth bounded 1-1000 rules with value 256",
    );
}

#[test]
fn test_protocol_analyzer_decode_layers_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("decode_layers", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "decode_layers >= 1 && decode_layers <= 7",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "decode_layers == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "decode_layers >= 1 && decode_layers <= 7",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protocol analyzer decode layers bounded 1-7 with value 4",
    );
}

#[test]
fn test_protocol_analyzer_protocol_layer_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("layer", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "layer >= 1 && layer <= 3"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "layer == 1 || layer == 2 || layer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protocol analyzer layer disjunction 1=physical 2=datalink 3=network",
    );
}

#[test]
fn test_protocol_analyzer_capture_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "mode >= 1 && mode <= 3"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protocol analyzer capture mode disjunction 1=full-duplex 2=half-duplex 3=tap",
    );
}

#[test]
fn test_protocol_analyzer_trigger_condition_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trig", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "trig >= 1 && trig <= 3"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "trig == 1 || trig == 2 || trig == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "protocol analyzer trigger condition disjunction 1=pattern-match 2=error-detect 3=threshold");
}

#[test]
fn test_protocol_analyzer_expert_analysis_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "expert",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protocol analyzer automatic expert analysis flag assumed 1 implies conditional equals 1",
    );
}
