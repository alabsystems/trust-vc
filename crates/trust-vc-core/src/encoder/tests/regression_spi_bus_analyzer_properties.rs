// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_clock_frequency_khz() {
    // SCLK frequency in kHz: value 10000 (10 MHz), min 100, max 100000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sclk_khz", u32_ty());
    ctx.declare_var_typed("freq_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "sclk_khz == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "freq_ok == if sclk_khz >= 100 && sclk_khz <= 100000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI: SCLK 10000 kHz (10 MHz) in [100, 100000]");
}

#[test]
fn test_data_width_bits() {
    // SPI data width: 4-way non-sequential (8, 16, 24, 32 bits)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("data_width", u32_ty());
    ctx.declare_var_typed("valid_dw", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "data_width == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_dw == if data_width == 8 || data_width == 16 || data_width == 24 || data_width == 32 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_dw == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI: data width 8 bits is valid in {8,16,24,32}");
}

#[test]
fn test_spi_mode_disjunction() {
    // SPI mode: 4-way disjunction (0=CPOL0/CPHA0, 1=CPOL0/CPHA1, 2=CPOL1/CPHA0, 3=CPOL1/CPHA1)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spi_mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "spi_mode == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if spi_mode == 0 || spi_mode == 1 || spi_mode == 2 || spi_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI: mode 0 (CPOL0/CPHA0) in {0,1,2,3}");
}

#[test]
fn test_capture_depth_samples() {
    // Capture buffer depth in samples: value 100000, min 1000, max 10000000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capture_depth", u32_ty());
    ctx.declare_var_typed("depth_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "capture_depth == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "depth_ok == if capture_depth >= 1000 && capture_depth <= 10000000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "depth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SPI: capture depth 100000 samples in [1000, 10000000]",
    );
}

#[test]
fn test_chip_select_lines() {
    // Number of chip select (CS) lines: value 4, min 1, max 16
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cs_lines", u32_ty());
    ctx.declare_var_typed("cs_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "cs_lines == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "cs_ok == if cs_lines >= 1 && cs_lines <= 16 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "cs_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI: 4 chip select lines in [1, 16]");
}

#[test]
fn test_bit_order_disjunction() {
    // Bit order: 2-way disjunction (1=MSB first, 2=LSB first)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bit_order", u32_ty());
    ctx.declare_var_typed("valid_bo", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "bit_order == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_bo == if bit_order == 1 || bit_order == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_bo == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI: bit order 1 (MSB first) in {1,2}");
}

#[test]
fn test_trigger_type_disjunction() {
    // Trigger type: 4-way disjunction (1=edge, 2=pattern, 3=protocol, 4=external)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trigger_type", u32_ty());
    ctx.declare_var_typed("valid_tt", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "trigger_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_tt == if trigger_type == 1 || trigger_type == 2 || trigger_type == 3 || trigger_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_tt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI: trigger type 3 (protocol) in {1,2,3,4}");
}

#[test]
fn test_input_voltage_threshold_mv() {
    // Logic level input voltage threshold in mV: value 1500, min 800, max 5000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("threshold_mv", u32_ty());
    ctx.declare_var_typed("thresh_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "threshold_mv == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "thresh_ok == if threshold_mv >= 800 && threshold_mv <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "thresh_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI: input threshold 1500 mV in [800, 5000]");
}

#[test]
fn test_sample_rate_mhz() {
    // Digital sample rate in MHz: value 200, min 10, max 1000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_rate", u32_ty());
    ctx.declare_var_typed("rate_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "sample_rate == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ok_def",
        "rate_ok == if sample_rate >= 10 && sample_rate <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI: sample rate 200 MHz in [10, 1000]");
}

#[test]
fn test_protocol_decode_boolean_flag() {
    // Protocol decode enabled flag (i32: 1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("decode_enabled", i32_ty());
    ctx.declare_var_typed("show_decoded", i32_ty());
    ctx.push_obligation(ProofObligation::assume("de", "decode_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sd_def",
        "show_decoded == if decode_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "show_decoded == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SPI: protocol decode flag 1 -> show decoded output",
    );
}
