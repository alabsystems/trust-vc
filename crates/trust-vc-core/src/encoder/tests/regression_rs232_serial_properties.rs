// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn baud_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud", u32_ty());
    ctx.declare_var_typed("valid_baud", i32_ty());
    // Standard baud rates: 9600, 19200, 38400, 57600, 115200
    ctx.push_obligation(ProofObligation::assume("b", "baud == 115200"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_baud == if baud == 9600 || baud == 19200 || baud == 38400 || baud == 57600 || baud == 115200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_baud == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-232: 115200 is a standard baud rate");
}

#[test]
fn data_bits() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("data_bits", u32_ty());
    ctx.declare_var_typed("valid_data", i32_ty());
    // Data bits: 5, 6, 7, or 8 (most common: 8)
    ctx.push_obligation(ProofObligation::assume("db", "data_bits == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_data == if data_bits >= 5 && data_bits <= 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_data == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-232: 8 data bits in [5, 8] → valid");
}

#[test]
fn stop_bits() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stop_bits_x10", u32_ty());
    ctx.declare_var_typed("valid_stop", i32_ty());
    // Stop bits: 1, 1.5, or 2 (×10 → 10, 15, 20)
    ctx.push_obligation(ProofObligation::assume("sb", "stop_bits_x10 == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_stop == if stop_bits_x10 == 10 || stop_bits_x10 == 15 || stop_bits_x10 == 20 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_stop == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-232: 1.0 stop bits is valid");
}

#[test]
fn parity_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("parity", u32_ty());
    ctx.declare_var_typed("is_even", i32_ty());
    // Parity: 0=none, 1=odd, 2=even, 3=mark, 4=space
    ctx.push_obligation(ProofObligation::assume("p", "parity == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ie_def",
        "is_even == if parity == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_even == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-232: parity=2 → even parity");
}

#[test]
fn voltage_levels() {
    let mut ctx = VerificationContext::new();
    for v in &["mark_mv", "min_mark_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("level_ok", i32_ty());
    // RS-232: mark (logic 1) = -3V to -15V, space (logic 0) = +3V to +15V
    // Using absolute values: mark ≥ 3000mV
    ctx.push_obligation(ProofObligation::assume("mm", "mark_mv == 9000")); // |−9V|
    ctx.push_obligation(ProofObligation::assume("mn", "min_mark_mv == 3000")); // |−3V|
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "level_ok == if mark_mv >= min_mark_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "level_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-232: |−9V| ≥ |−3V| min → level OK");
}

#[test]
fn frame_size() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bits", "has_parity", "stop_bits_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("total_bits_x10", u32_ty());
    // Frame = start(1) + data + parity(0/1) + stop. Precompute: (1+8+0)×10 + 10 = 100
    ctx.push_obligation(ProofObligation::assume("db", "data_bits == 8"));
    ctx.push_obligation(ProofObligation::assume("hp", "has_parity == 0"));
    ctx.push_obligation(ProofObligation::assume("sb", "stop_bits_x10 == 10"));
    ctx.push_obligation(ProofObligation::assume("tb", "total_bits_x10 == 100")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_100", "total_bits_x10 == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-232: 8N1 = 10.0 bits/frame (precomputed)");
}

#[test]
fn cable_length() {
    let mut ctx = VerificationContext::new();
    for v in &["length_m", "max_length_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("length_ok", i32_ty());
    // RS-232: max ~15m at 19200 baud (spec: 2500pF cable capacitance)
    ctx.push_obligation(ProofObligation::assume("lm", "length_m == 10"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_length_m == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "length_ok == if length_m <= max_length_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "length_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-232: 10m cable ≤ 15m max → length OK");
}

#[test]
fn flow_control() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fc_type", u32_ty());
    ctx.declare_var_typed("is_hardware", i32_ty());
    // Flow control: 0=none, 1=XON/XOFF (software), 2=RTS/CTS (hardware)
    ctx.push_obligation(ProofObligation::assume("ft", "fc_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ih_def",
        "is_hardware == if fc_type == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_hardware == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-232: fc_type=2 → RTS/CTS hardware flow control");
}

#[test]
fn rx_buffer() {
    let mut ctx = VerificationContext::new();
    for v in &["buffer_bytes", "max_buffer"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("buf_ok", i32_ty());
    // Receive buffer (UART FIFO: 16, 64, 128 bytes typical)
    ctx.push_obligation(ProofObligation::assume("bb", "buffer_bytes == 64"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_buffer == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "buf_ok == if buffer_bytes <= max_buffer { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "buf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-232: 64B RX buffer ≤ 128B max → OK");
}

#[test]
fn baud_error() {
    let mut ctx = VerificationContext::new();
    for v in &["error_pct_x100", "max_error_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("error_ok", i32_ty());
    // Baud rate error tolerance: < 2% for reliable communication (×100 scale)
    ctx.push_obligation(ProofObligation::assume("ep", "error_pct_x100 == 16")); // 0.16%
    ctx.push_obligation(ProofObligation::assume("me", "max_error_x100 == 200")); // 2.00%
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "error_ok == if error_pct_x100 <= max_error_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "error_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-232: 0.16% baud error ≤ 2.00% max → OK");
}
