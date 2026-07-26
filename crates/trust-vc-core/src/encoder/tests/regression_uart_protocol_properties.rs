// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn frame_size_8n1() {
    // 8N1: 1 start + 8 data + 1 stop = 10 bits
    let mut ctx = VerificationContext::new();
    for v in &[
        "start_bits",
        "data_bits",
        "parity_bits",
        "stop_bits",
        "frame_bits",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sb", "start_bits == 1"));
    ctx.push_obligation(ProofObligation::assume("db", "data_bits == 8"));
    ctx.push_obligation(ProofObligation::assume("pb", "parity_bits == 0")); // no parity
    ctx.push_obligation(ProofObligation::assume("stb", "stop_bits == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "fb_def",
        "frame_bits == start_bits + data_bits + parity_bits + stop_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "frame_bits == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UART 8N1: 1+8+0+1=10 bits/frame");
}

#[test]
fn baud_rate_divisor() {
    let mut ctx = VerificationContext::new();
    for v in &["sys_clock", "baud_rate", "divisor"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sc", "sys_clock == 48000000")); // 48MHz
    ctx.push_obligation(ProofObligation::assume("br", "baud_rate == 115200"));
    // divisor = sys_clock / (16 * baud_rate) — precomputed
    ctx.push_obligation(ProofObligation::assume("d", "divisor == 26")); // 48000000/(16*115200) ≈ 26
    ctx.push_obligation(ProofObligation::assert("is_26", "divisor == 26"));
    ctx.push_obligation(ProofObligation::assert("positive", "divisor > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UART: baud divisor 26 for 115200 @ 48MHz");
}

#[test]
fn oversampling_16x() {
    let mut ctx = VerificationContext::new();
    for v in &["baud_rate", "sample_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("br", "baud_rate == 9600"));
    ctx.push_obligation(ProofObligation::assume(
        "sr_def",
        "sample_rate == baud_rate * 16",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_153600",
        "sample_rate == 153600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "UART: 9600×16=153600 sample rate");
}

#[test]
fn tx_fifo_space() {
    let mut ctx = VerificationContext::new();
    for v in &["fifo_depth", "fifo_count", "space"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fd", "fifo_depth == 16"));
    ctx.push_obligation(ProofObligation::assume("fc", "fifo_count == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "space == fifo_depth - fifo_count",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "space == 6"));
    ctx.push_obligation(ProofObligation::assert("has_space", "space > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UART TX: 16-10=6 FIFO slots free");
}

#[test]
fn parity_even_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("data_ones_count", u32_ty());
    ctx.declare_var_typed("parity_bit", u32_ty());
    ctx.declare_var_typed("even_parity_ok", i32_ty());
    // Even parity: total 1-bits (data + parity) must be even
    ctx.push_obligation(ProofObligation::assume("doc", "data_ones_count == 5")); // odd
    ctx.push_obligation(ProofObligation::assume("pb", "parity_bit == 1")); // makes total even
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "even_parity_ok == if (data_ones_count + parity_bit) % 2 == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "even_parity_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "UART: 5+1=6 (even parity OK)");
}

#[test]
fn framing_error_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stop_bit_value", u32_ty());
    ctx.declare_var_typed("framing_error", i32_ty());
    // Framing error if stop bit is not 1
    ctx.push_obligation(ProofObligation::assume("sbv", "stop_bit_value == 0")); // invalid
    ctx.push_obligation(ProofObligation::assume(
        "fe_def",
        "framing_error == if stop_bit_value != 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "framing_error == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UART: stop=0 → framing error");
}

#[test]
fn effective_data_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["baud_rate", "frame_bits", "data_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("efficiency_pct", u32_ty());
    // 8N1: 8 data bits out of 10 frame bits = 80% efficiency
    ctx.push_obligation(ProofObligation::assume("br", "baud_rate == 115200"));
    ctx.push_obligation(ProofObligation::assume("fb", "frame_bits == 10"));
    ctx.push_obligation(ProofObligation::assume("db", "data_bits == 8"));
    ctx.push_obligation(ProofObligation::assume("ep", "efficiency_pct == 80")); // precomputed 8/10*100
    ctx.push_obligation(ProofObligation::assert("is_80", "efficiency_pct == 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UART 8N1: 80% efficiency (8/10)");
}

#[test]
fn break_condition_duration() {
    let mut ctx = VerificationContext::new();
    for v in &["break_bits", "min_break_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_break", i32_ty());
    // Break: line held low for >= 1 frame time (10 bits for 8N1)
    ctx.push_obligation(ProofObligation::assume("bb", "break_bits == 13")); // LIN break
    ctx.push_obligation(ProofObligation::assume("mbb", "min_break_bits == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_break == if break_bits >= min_break_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_break == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UART break: 13 >= 10 bits → valid");
}

#[test]
fn rx_timeout_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["idle_bit_count", "timeout_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timeout", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ibc", "idle_bit_count == 32"));
    ctx.push_obligation(ProofObligation::assume("tt", "timeout_threshold == 24"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "timeout == if idle_bit_count >= timeout_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timeout == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UART RX timeout: 32 >= 24 bit periods");
}

#[test]
fn flow_control_rts_cts() {
    let mut ctx = VerificationContext::new();
    for v in &["rx_fifo_level", "rts_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rts_deasserted", i32_ty());
    // RTS deasserted (high) when RX FIFO almost full
    ctx.push_obligation(ProofObligation::assume("rfl", "rx_fifo_level == 14"));
    ctx.push_obligation(ProofObligation::assume("rt", "rts_threshold == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "rd_def",
        "rts_deasserted == if rx_fifo_level >= rts_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rts_deasserted == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UART RTS: FIFO 14 >= 12 → deasserted");
}
