// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_ic_column_length_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("col_len", i32_ty());
    ctx.push_obligation(ProofObligation::assume("col_len_val", "col_len == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "col_len_bounded",
        "col_len >= 50 && col_len <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column length 250 mm in [50, 500]");
}

#[test]
fn test_ic_flow_rate_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow >= 1 && flow <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 100 (1.00 mL/min) in [1, 5000]");
}

#[test]
fn test_ic_max_pressure_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pressure_val", "pressure == 4000"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure >= 100 && pressure <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure 4000 (400.0 bar) in [100, 10000]");
}

#[test]
fn test_ic_detection_limit_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("det_limit_val", "det_limit == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "det_limit_bounded",
        "det_limit >= 1 && det_limit <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection limit 10 (0.10 ppb) in [1, 10000]");
}

#[test]
fn test_ic_sample_volume_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume", i32_ty());
    ctx.push_obligation(ProofObligation::assume("volume_val", "volume == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "volume_bounded",
        "volume >= 1 && volume <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample volume 250 (25.0 uL) in [1, 10000]");
}

#[test]
fn test_ic_number_of_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume("channels_val", "channels == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "channels_bounded",
        "channels >= 1 && channels <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of channels 2 in [1, 8]");
}

#[test]
fn test_ic_suppression_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("suppression", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "suppression_val",
        "suppression == 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "suppression_valid",
        "suppression == 1 || suppression == 2 || suppression == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "suppression 2=electrolytic in {1=chemical, 2=electrolytic, 3=membrane}",
    );
}

#[test]
fn test_ic_detection_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume("method_val", "method == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "method_valid",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection method 1=conductivity in {1=conductivity, 2=UV-Vis, 3=amperometric}",
    );
}

#[test]
fn test_ic_eluent_generation_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eluent", i32_ty());
    ctx.push_obligation(ProofObligation::assume("eluent_val", "eluent == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "eluent_valid",
        "eluent == 1 || eluent == 2 || eluent == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "eluent generation 2=electrolytic in {1=manual, 2=electrolytic, 3=gradient-pump}",
    );
}

#[test]
fn test_ic_automatic_eluent_regeneration_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "regeneration_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic eluent regeneration flag=1 yields active (1)",
    );
}
