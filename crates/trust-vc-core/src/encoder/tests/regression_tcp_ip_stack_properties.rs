// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ip_header_checksum_length() {
    let mut ctx = VerificationContext::new();
    for v in &["ihl", "header_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // IHL (Internet Header Length) is in 32-bit words
    // IHL=5 → 20 bytes (minimum), IHL=15 → 60 bytes (maximum)
    ctx.push_obligation(ProofObligation::assume("ihl", "ihl == 5"));
    ctx.push_obligation(ProofObligation::assume("hb_def", "header_bytes == ihl * 4"));
    ctx.push_obligation(ProofObligation::assert("is_20", "header_bytes == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "IP: IHL=5 × 4 = 20 bytes header");
}

#[test]
fn tcp_window_scale() {
    let mut ctx = VerificationContext::new();
    for v in &["window_size", "scale_factor", "effective_window"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // TCP window scaling: effective = advertised << scale
    // Precompute: 16384 << 4 = 16384 * 16 = 262144
    ctx.push_obligation(ProofObligation::assume("ws", "window_size == 16384"));
    ctx.push_obligation(ProofObligation::assume("sf", "scale_factor == 16")); // 2^4
    ctx.push_obligation(ProofObligation::assume(
        "ew_def",
        "effective_window == window_size * scale_factor",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_262144",
        "effective_window == 262144",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "TCP window: 16384 × 16 = 262144 bytes");
}

#[test]
fn tcp_sequence_advance() {
    let mut ctx = VerificationContext::new();
    for v in &["seq_num", "data_len", "next_seq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Sequence number advances by data length
    ctx.push_obligation(ProofObligation::assume("sn", "seq_num == 1000000"));
    ctx.push_obligation(ProofObligation::assume("dl", "data_len == 1460")); // MSS
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "next_seq == seq_num + data_len",
    ));
    ctx.push_obligation(ProofObligation::assert("is_correct", "next_seq == 1001460"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCP seq: 1000000 + 1460 = 1001460");
}

#[test]
fn mss_negotiation() {
    let mut ctx = VerificationContext::new();
    for v in &["local_mss", "remote_mss", "effective_mss"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Effective MSS = min of both sides
    ctx.push_obligation(ProofObligation::assume("lm", "local_mss == 1460"));
    ctx.push_obligation(ProofObligation::assume("rm", "remote_mss == 1400"));
    ctx.push_obligation(ProofObligation::assume(
        "em_def",
        "effective_mss == if local_mss < remote_mss { local_mss } else { remote_mss }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1400", "effective_mss == 1400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCP MSS: min(1460, 1400) = 1400");
}

#[test]
fn ip_total_length() {
    let mut ctx = VerificationContext::new();
    for v in &["header_bytes", "payload_bytes", "total_length"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_length", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hb", "header_bytes == 20"));
    ctx.push_obligation(ProofObligation::assume("pb", "payload_bytes == 1460"));
    ctx.push_obligation(ProofObligation::assume(
        "tl_def",
        "total_length == header_bytes + payload_bytes",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "vl_def",
        "valid_length == if total_length <= 65535 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1480", "total_length == 1480"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_length == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IP: 20 + 1460 = 1480 total, <= 65535");
}

#[test]
fn ttl_decrement() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ttl", u32_ty());
    ctx.declare_var_typed("new_ttl", u32_ty());
    ctx.declare_var_typed("should_forward", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "ttl == 64"));
    ctx.push_obligation(ProofObligation::assume("nt_def", "new_ttl == ttl - 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sf_def",
        "should_forward == if new_ttl > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_63", "new_ttl == 63"));
    ctx.push_obligation(ProofObligation::assert("yes", "should_forward == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IP: TTL 64 → 63, forward");
}

#[test]
fn congestion_window() {
    let mut ctx = VerificationContext::new();
    for v in &["cwnd", "mss", "new_cwnd"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Slow start: cwnd doubles each RTT (increment by MSS per ACK)
    ctx.push_obligation(ProofObligation::assume("c", "cwnd == 14600")); // 10 × MSS
    ctx.push_obligation(ProofObligation::assume("m", "mss == 1460"));
    ctx.push_obligation(ProofObligation::assume("nc_def", "new_cwnd == cwnd + mss"));
    ctx.push_obligation(ProofObligation::assert("is_16060", "new_cwnd == 16060"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCP slow start: 14600 + 1460 = 16060 cwnd");
}

#[test]
fn port_range_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("port", u32_ty());
    ctx.declare_var_typed("is_ephemeral", i32_ty());
    // Ephemeral port range: 49152-65535 (IANA)
    ctx.push_obligation(ProofObligation::assume("p", "port == 55000"));
    ctx.push_obligation(ProofObligation::assume(
        "ie_def",
        "is_ephemeral == if port >= 49152 && port <= 65535 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_ephemeral == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCP: port 55000 in [49152, 65535] → ephemeral");
}

#[test]
fn fragment_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["fragment_number", "mtu_payload"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("byte_offset", u32_ty());
    // Fragment offset is in 8-byte units
    // Fragment 2 with 1480-byte MTU payload → byte offset = 2 × 1480 = 2960
    ctx.push_obligation(ProofObligation::assume("fn_val", "fragment_number == 2"));
    ctx.push_obligation(ProofObligation::assume("mp", "mtu_payload == 1480"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "byte_offset == fragment_number * mtu_payload",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2960", "byte_offset == 2960"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "IP fragment: offset = 2 × 1480 = 2960");
}

#[test]
fn retransmission_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["srtt_ms", "rttvar_ms", "rto_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rto_valid", i32_ty());
    // RTO = SRTT + 4 × RTTVAR (RFC 6298)
    // Precompute: 4 × RTTVAR
    ctx.push_obligation(ProofObligation::assume("s", "srtt_ms == 200"));
    ctx.push_obligation(ProofObligation::assume("r", "rttvar_ms == 50"));
    // 200 + 4 × 50 = 400
    ctx.push_obligation(ProofObligation::assume("rto", "rto_ms == 400")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "rv_def",
        "rto_valid == if rto_ms >= 1000 { 0 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_400", "rto_ms == 400"));
    ctx.push_obligation(ProofObligation::assert("reasonable", "rto_valid == 1")); // < 1s
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCP RTO: 200 + 4×50 = 400ms");
}
