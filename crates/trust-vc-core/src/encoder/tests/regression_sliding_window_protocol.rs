// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn window_size_limits_outstanding() {
    let mut ctx = VerificationContext::new();
    for v in &["window_size", "sent", "acked", "outstanding"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_send", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ws", "window_size == 8"));
    ctx.push_obligation(ProofObligation::assume("s", "sent == 20"));
    ctx.push_obligation(ProofObligation::assume("a", "acked == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "outstanding == sent - acked",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "can_send == if outstanding < window_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "outstanding == 5"));
    ctx.push_obligation(ProofObligation::assert("yes", "can_send == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "window: 20-15=5 outstanding < 8 → can send");
}

#[test]
fn window_full_blocks_sender() {
    let mut ctx = VerificationContext::new();
    for v in &["window_size", "sent", "acked", "outstanding"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_send", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ws", "window_size == 4"));
    ctx.push_obligation(ProofObligation::assume("s", "sent == 10"));
    ctx.push_obligation(ProofObligation::assume("a", "acked == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "outstanding == sent - acked",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "can_send == if outstanding < window_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "outstanding == 4"));
    ctx.push_obligation(ProofObligation::assert("blocked", "can_send == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "window full: 10-6=4 = window_size → blocked");
}

#[test]
fn ack_advances_window() {
    let mut ctx = VerificationContext::new();
    for v in &["old_ack", "new_ack", "window_advance"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oa", "old_ack == 10"));
    ctx.push_obligation(ProofObligation::assume("na", "new_ack == 13"));
    ctx.push_obligation(ProofObligation::assume(
        "wa_def",
        "window_advance == new_ack - old_ack",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "window_advance == 3"));
    ctx.push_obligation(ProofObligation::assert("forward", "new_ack > old_ack"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ack advance: 13 - 10 = 3 slots freed");
}

#[test]
fn sequence_number_space() {
    // Sequence numbers must be >= 2 * window_size to avoid ambiguity
    let mut ctx = VerificationContext::new();
    for v in &["window_size", "seq_space", "min_seq_space"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sufficient", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ws", "window_size == 8"));
    ctx.push_obligation(ProofObligation::assume("ss", "seq_space == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "mss_def",
        "min_seq_space == 2 * window_size",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "suf_def",
        "sufficient == if seq_space >= min_seq_space { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "min_seq_space == 16"));
    ctx.push_obligation(ProofObligation::assert("ok", "sufficient == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "seq space: 16 >= 2*8 → sufficient");
}

#[test]
fn go_back_n_retransmit_count() {
    let mut ctx = VerificationContext::new();
    for v in &["window_size", "lost_seq", "next_seq", "retransmit_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ws", "window_size == 8"));
    ctx.push_obligation(ProofObligation::assume("ls", "lost_seq == 5"));
    ctx.push_obligation(ProofObligation::assume("ns", "next_seq == 10"));
    // Go-Back-N retransmits everything from lost_seq to next_seq-1
    ctx.push_obligation(ProofObligation::assume(
        "rc_def",
        "retransmit_count == next_seq - lost_seq",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "retransmit_count == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "within_window",
        "retransmit_count <= window_size",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GBN: retransmit 10-5=5 packets, within window 8");
}

#[test]
fn selective_repeat_retransmit() {
    // Only the lost packet is retransmitted
    let mut ctx = VerificationContext::new();
    for v in &["total_outstanding", "lost_packets", "retransmit_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("to", "total_outstanding == 8"));
    ctx.push_obligation(ProofObligation::assume("lp", "lost_packets == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "rc_def",
        "retransmit_count == lost_packets",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "retransmit_count == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "fewer",
        "retransmit_count < total_outstanding",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SR: only 1 lost packet retransmitted out of 8");
}

#[test]
fn throughput_with_window() {
    // Throughput = window_size * packet_size / RTT
    // Simplified: compute window_bytes = window_size * packet_size
    let mut ctx = VerificationContext::new();
    for v in &["window_size", "packet_size", "window_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ws", "window_size == 10"));
    ctx.push_obligation(ProofObligation::assume("ps", "packet_size == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "window_bytes == window_size * packet_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15000", "window_bytes == 15000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "throughput: 10 × 1500 = 15000 bytes/RTT");
}

#[test]
fn cumulative_ack_covers_range() {
    let mut ctx = VerificationContext::new();
    for v in &["cum_ack", "first_unacked", "packets_acked"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ca", "cum_ack == 25"));
    ctx.push_obligation(ProofObligation::assume("fu", "first_unacked == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "pa_def",
        "packets_acked == cum_ack - first_unacked",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "packets_acked == 5"));
    ctx.push_obligation(ProofObligation::assert("positive", "packets_acked > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cumulative ACK: 25-20 = 5 packets acknowledged");
}

#[test]
fn timeout_retransmission() {
    let mut ctx = VerificationContext::new();
    for v in &["rtt_estimate", "rtt_variance", "rto"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // RTO = RTT + 4 * variance (simplified)
    ctx.push_obligation(ProofObligation::assume("re", "rtt_estimate == 100")); // 100ms
    ctx.push_obligation(ProofObligation::assume("rv", "rtt_variance == 25")); // 25ms
    ctx.push_obligation(ProofObligation::assume(
        "rto_def",
        "rto == rtt_estimate + 4 * rtt_variance",
    ));
    ctx.push_obligation(ProofObligation::assert("is_200", "rto == 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RTO: 100 + 4*25 = 200ms");
}

#[test]
fn receiver_buffer_occupancy() {
    let mut ctx = VerificationContext::new();
    for v in &["received_total", "delivered", "buffered", "buffer_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_space", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rt", "received_total == 100"));
    ctx.push_obligation(ProofObligation::assume("d", "delivered == 85"));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "buffered == received_total - delivered",
    ));
    ctx.push_obligation(ProofObligation::assume("bc", "buffer_capacity == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "hs_def",
        "has_space == if buffered < buffer_capacity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "buffered == 15"));
    ctx.push_obligation(ProofObligation::assert("ok", "has_space == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "buffer: 100-85=15 buffered < 32 capacity");
}
