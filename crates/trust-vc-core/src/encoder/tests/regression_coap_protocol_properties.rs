// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn message_size() {
    let mut ctx = VerificationContext::new();
    for v in &["msg_bytes", "max_msg_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("msg_ok", i32_ty());
    // CoAP message size (fits in single UDP datagram)
    ctx.push_obligation(ProofObligation::assume("mb", "msg_bytes == 128"));
    ctx.push_obligation(ProofObligation::assume("mm", "max_msg_bytes == 1152")); // typical MTU limit
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "msg_ok == if msg_bytes <= max_msg_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "msg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoAP: 128-byte message ≤ 1152 max → OK");
}

#[test]
fn message_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("msg_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // CoAP message types: 0=CON, 1=NON, 2=ACK, 3=RST
    ctx.push_obligation(ProofObligation::assume("mt", "msg_type == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_type == if msg_type == 0 || msg_type == 1 || msg_type == 2 || msg_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoAP: CON is valid message type");
}

#[test]
fn token_length() {
    let mut ctx = VerificationContext::new();
    for v in &["token_len", "max_token_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tok_ok", i32_ty());
    // Token length: 0-8 bytes
    ctx.push_obligation(ProofObligation::assume("tl", "token_len == 4"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_token_len == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tok_ok == if token_len <= max_token_len { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tok_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoAP: 4-byte token ≤ 8 max → OK");
}

#[test]
fn retransmit_count() {
    let mut ctx = VerificationContext::new();
    for v in &["retransmits", "max_retransmits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ret_ok", i32_ty());
    // MAX_RETRANSMIT default = 4
    ctx.push_obligation(ProofObligation::assume("r", "retransmits == 4"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_retransmits == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ret_ok == if retransmits <= max_retransmits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ret_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoAP: 4 retransmits ≤ 10 max → OK");
}

#[test]
fn observe_sequence() {
    let mut ctx = VerificationContext::new();
    for v in &["seq_num", "max_seq_num"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("seq_ok", i32_ty());
    // Observe option: 24-bit sequence number
    ctx.push_obligation(ProofObligation::assume("sn", "seq_num == 100"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_seq_num == 16777215")); // 2^24 - 1
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "seq_ok == if seq_num <= max_seq_num { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "seq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoAP: observe seq 100 ≤ 16777215 (24-bit) → OK");
}

#[test]
fn block_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("szx", u32_ty());
    ctx.declare_var_typed("valid_szx", i32_ty());
    // Block size exponent (SZX): 0-6 → 16-1024 bytes
    ctx.push_obligation(ProofObligation::assume("s", "szx == 4")); // 256 bytes
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_szx == if szx == 0 || szx == 1 || szx == 2 || szx == 3 || szx == 4 || szx == 5 || szx == 6 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_szx == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoAP: SZX 4 (256B) is valid block size");
}

#[test]
fn content_format() {
    let mut ctx = VerificationContext::new();
    for v in &["format_id", "max_format_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fmt_ok", i32_ty());
    // Content-Format option (16-bit)
    ctx.push_obligation(ProofObligation::assume("fi", "format_id == 50")); // JSON
    ctx.push_obligation(ProofObligation::assume("mf", "max_format_id == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "fmt_ok == if format_id <= max_format_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fmt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoAP: format 50 (JSON) ≤ 65535 → OK");
}

#[test]
fn ack_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["timeout_ms", "min_timeout_ms", "max_timeout_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ack_ok", i32_ty());
    // ACK_TIMEOUT (default 2000ms)
    ctx.push_obligation(ProofObligation::assume("tm", "timeout_ms == 2000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_timeout_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_timeout_ms == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "ack_ok == if timeout_ms >= min_timeout_ms && timeout_ms <= max_timeout_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ack_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoAP: 2000ms ACK timeout in [1000, 10000] → OK");
}

#[test]
fn uri_path_length() {
    let mut ctx = VerificationContext::new();
    for v in &["path_len", "max_path_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("path_ok", i32_ty());
    // URI path segment length (max 255 per segment)
    ctx.push_obligation(ProofObligation::assume("pl", "path_len == 32"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_path_len == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "path_ok == if path_len >= 1 && path_len <= max_path_len { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "path_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoAP: 32-byte URI path in [1, 255] → OK");
}

#[test]
fn nstart() {
    let mut ctx = VerificationContext::new();
    for v in &["nstart", "max_nstart"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ns_ok", i32_ty());
    // NSTART: max outstanding CON interactions (default 1)
    ctx.push_obligation(ProofObligation::assume("n", "nstart == 1"));
    ctx.push_obligation(ProofObligation::assume("mn", "max_nstart == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "ns_ok == if nstart >= 1 && nstart <= max_nstart { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ns_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoAP: NSTART 1 in [1, 5] → OK");
}
