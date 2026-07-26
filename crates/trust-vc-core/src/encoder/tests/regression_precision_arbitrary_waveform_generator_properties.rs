// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates Apache 2.0
// Precision arbitrary waveform generator property regression tests

use super::*;

#[test]
fn test_sample_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sample_rate >= 100 && sample_rate <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "sample_rate == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sample_rate >= 100 && sample_rate <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample rate 5000 MSa/s within 100-20000 MSa/s bounds",
    );
}

#[test]
fn test_vertical_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vertical_resolution", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "vertical_resolution >= 8 && vertical_resolution <= 16",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "vertical_resolution == 14"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "vertical_resolution >= 8 && vertical_resolution <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vertical resolution 14 bits within 8-16 bit bounds",
    );
}

#[test]
fn test_memory_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("memory_depth", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "memory_depth >= 1000 && memory_depth <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "memory_depth == 64000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "memory_depth >= 1000 && memory_depth <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "memory depth 64000 kSa within 1000-1000000 kSa bounds",
    );
}

#[test]
fn test_output_amplitude_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_amplitude_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "output_amplitude_x1000 >= 1 && output_amplitude_x1000 <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "output_amplitude_x1000 == 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "output_amplitude_x1000 >= 1 && output_amplitude_x1000 <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "output amplitude 10000 (10.000 Vpp) within 1-20000 x1000 Vpp bounds",
    );
}

#[test]
fn test_frequency_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frequency_max", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "frequency_max >= 1 && frequency_max <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "frequency_max == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "frequency_max >= 1 && frequency_max <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency max 250 MHz within 1-1000 MHz bounds");
}

#[test]
fn test_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channels >= 1 && channels <= 8",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "channels == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "channels >= 1 && channels <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channels 2 within 1-8 output channel bounds");
}

#[test]
fn test_modulation_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("modulation_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "modulation_type >= 1 && modulation_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "modulation_type == 1 || modulation_type == 2 || modulation_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "modulation type is AM(1), FM(2), or PM(3)");
}

#[test]
fn test_output_filter_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_filter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "output_filter >= 1 && output_filter <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "output_filter == 1 || output_filter == 2 || output_filter == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "output filter is elliptic(1), bessel(2), or none(3)",
    );
}

#[test]
fn test_clock_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("clock_source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "clock_source >= 1 && clock_source <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "clock_source == 1 || clock_source == 2 || clock_source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "clock source is internal(1), external(2), or PLL(3)",
    );
}

#[test]
fn test_differential_output_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "diff_out",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "differential output flag enabled when flag is 1");
}
