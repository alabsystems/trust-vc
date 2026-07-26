// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn max_packet_size_control() {
    let mut ctx = VerificationContext::new();
    for v in &["speed", "max_packet"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Full-speed control: max 64 bytes
    ctx.push_obligation(ProofObligation::assume("s", "speed == 1")); // 0=low, 1=full, 2=high
    ctx.push_obligation(ProofObligation::assume("mp", "max_packet == 64"));
    ctx.push_obligation(ProofObligation::assert("is_64", "max_packet == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB: full-speed control → 64 bytes max");
}

#[test]
fn bulk_endpoint_throughput() {
    let mut ctx = VerificationContext::new();
    for v in &["max_packet", "packets_per_frame", "bytes_per_frame"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Full-speed bulk: up to 19 packets per 1ms frame × 64 bytes
    ctx.push_obligation(ProofObligation::assume("mp", "max_packet == 64"));
    ctx.push_obligation(ProofObligation::assume("ppf", "packets_per_frame == 19"));
    ctx.push_obligation(ProofObligation::assume(
        "bpf_def",
        "bytes_per_frame == max_packet * packets_per_frame",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_1216",
        "bytes_per_frame == 1216",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "USB bulk: 64×19=1216 bytes/frame");
}

#[test]
fn endpoint_address_direction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ep_address", u32_ty());
    ctx.declare_var_typed("ep_number", u32_ty());
    ctx.declare_var_typed("is_in", i32_ty());
    // Bit 7: 1=IN (device to host), 0=OUT (host to device)
    // EP address 0x81 = EP 1 IN
    ctx.push_obligation(ProofObligation::assume("ea", "ep_address == 129")); // 0x81
    ctx.push_obligation(ProofObligation::assume("en", "ep_number == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ii_def",
        "is_in == if ep_address >= 128 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("in_dir", "is_in == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB: EP 0x81 → IN direction");
}

#[test]
fn isochronous_bandwidth_reservation() {
    let mut ctx = VerificationContext::new();
    for v in &["reserved_bytes", "frame_capacity", "available"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Full-speed: 1023 bytes max per 1ms frame for isochronous
    ctx.push_obligation(ProofObligation::assume("rb", "reserved_bytes == 512"));
    ctx.push_obligation(ProofObligation::assume("fc", "frame_capacity == 1023"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "available == frame_capacity - reserved_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_511", "available == 511"));
    ctx.push_obligation(ProofObligation::assert("has_room", "available > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB iso: 1023-512=511 bytes available");
}

#[test]
fn data_toggle_alternation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_toggle", u32_ty());
    ctx.declare_var_typed("next_toggle", u32_ty());
    // DATA0/DATA1 alternates on each successful transfer
    ctx.push_obligation(ProofObligation::assume("ct", "current_toggle == 0")); // DATA0
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "next_toggle == 1 - current_toggle",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "next_toggle == 1")); // DATA1
    ctx.push_obligation(ProofObligation::assert(
        "flipped",
        "next_toggle != current_toggle",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB toggle: DATA0 → DATA1");
}

#[test]
fn setup_packet_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("setup_bytes", u32_ty());
    ctx.declare_var_typed("expected_size", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // SETUP packets are always exactly 8 bytes
    ctx.push_obligation(ProofObligation::assume("sb", "setup_bytes == 8"));
    ctx.push_obligation(ProofObligation::assume("es", "expected_size == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if setup_bytes == expected_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB SETUP: 8 bytes (fixed)");
}

#[test]
fn fifo_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "rx_fifo_words",
        "tx_ep0_words",
        "tx_ep1_words",
        "total_words",
        "max_fifo",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rx", "rx_fifo_words == 128"));
    ctx.push_obligation(ProofObligation::assume("tx0", "tx_ep0_words == 64"));
    ctx.push_obligation(ProofObligation::assume("tx1", "tx_ep1_words == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total_words == rx_fifo_words + tx_ep0_words + tx_ep1_words",
    ));
    ctx.push_obligation(ProofObligation::assume("mf", "max_fifo == 320")); // total available
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fits == if total_words <= max_fifo { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_256", "total_words == 256"));
    ctx.push_obligation(ProofObligation::assert("ok", "fits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB FIFO: 128+64+64=256 <= 320");
}

#[test]
fn nak_handshake() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("buffer_ready", u32_ty());
    ctx.declare_var_typed("send_nak", i32_ty());
    // NAK when endpoint has no data ready
    ctx.push_obligation(ProofObligation::assume("br", "buffer_ready == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "sn_def",
        "send_nak == if buffer_ready == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "send_nak == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB: buffer not ready → NAK");
}

#[test]
fn stall_condition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("request_valid", u32_ty());
    ctx.declare_var_typed("feature_supported", u32_ty());
    ctx.declare_var_typed("send_stall", i32_ty());
    // STALL when request is invalid or unsupported
    ctx.push_obligation(ProofObligation::assume("rv", "request_valid == 1"));
    ctx.push_obligation(ProofObligation::assume("fs", "feature_supported == 0")); // not supported
    ctx.push_obligation(ProofObligation::assume(
        "ss_def",
        "send_stall == if request_valid == 0 || feature_supported == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "send_stall == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB: unsupported feature → STALL");
}

#[test]
fn suspend_detect() {
    let mut ctx = VerificationContext::new();
    for v in &["idle_ms", "suspend_threshold_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("suspended", i32_ty());
    // USB suspend: no bus activity for 3ms
    ctx.push_obligation(ProofObligation::assume("im", "idle_ms == 5"));
    ctx.push_obligation(ProofObligation::assume("st", "suspend_threshold_ms == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "suspended == if idle_ms >= suspend_threshold_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "suspended == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "USB: 5ms idle >= 3ms → suspended");
}
