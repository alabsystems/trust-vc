// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn slow_start_doubles_cwnd() {
    let mut ctx = VerificationContext::new();
    for v in &["cwnd_before", "acked", "cwnd_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cb", "cwnd_before == 10")); // MSS units
    ctx.push_obligation(ProofObligation::assume("a", "acked == 10")); // full window ACKed
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "cwnd_after == cwnd_before + acked",
    )); // +1 MSS per ACK
    ctx.push_obligation(ProofObligation::assert("is_20", "cwnd_after == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "slow start: cwnd 10 → 20 (doubles)");
}

#[test]
fn congestion_avoidance_linear_increase() {
    let mut ctx = VerificationContext::new();
    for v in &["cwnd_before", "cwnd_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cb", "cwnd_before == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "cwnd_after == cwnd_before + 1",
    )); // AIMD: +1 per RTT
    ctx.push_obligation(ProofObligation::assert("is_21", "cwnd_after == 21"));
    ctx.push_obligation(ProofObligation::assert(
        "linear",
        "cwnd_after == cwnd_before + 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "congestion avoidance: cwnd 20 → 21 (linear)");
}

#[test]
fn multiplicative_decrease_on_loss() {
    let mut ctx = VerificationContext::new();
    for v in &["cwnd_before", "cwnd_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cb", "cwnd_before == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "cwnd_after == cwnd_before / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "cwnd_after == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "AIMD decrease: cwnd 20 → 10 (halved)");
}

#[test]
fn ssthresh_set_on_loss() {
    let mut ctx = VerificationContext::new();
    for v in &["cwnd_at_loss", "new_ssthresh"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cal", "cwnd_at_loss == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "new_ssthresh == cwnd_at_loss / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_20", "new_ssthresh == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ssthresh: 40/2 = 20 on loss");
}

#[test]
fn slow_start_to_congestion_avoidance_transition() {
    let mut ctx = VerificationContext::new();
    for v in &["cwnd", "ssthresh"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_slow_start", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c", "cwnd == 20"));
    ctx.push_obligation(ProofObligation::assume("s", "ssthresh == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "iss_def",
        "in_slow_start == if cwnd < ssthresh { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ca_mode", "in_slow_start == 0")); // in congestion avoidance
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cwnd 20 >= ssthresh 16 → congestion avoidance");
}

#[test]
fn flight_size_within_cwnd() {
    let mut ctx = VerificationContext::new();
    for v in &["bytes_in_flight", "cwnd"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_send", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bif", "bytes_in_flight == 8000"));
    ctx.push_obligation(ProofObligation::assume("c", "cwnd == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "can_send == if bytes_in_flight < cwnd { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "can_send == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "8000 in flight < cwnd 10000 → can send");
}

#[test]
fn rto_doubles_on_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["rto_before", "rto_after", "max_rto"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rb", "rto_before == 1000")); // ms
    ctx.push_obligation(ProofObligation::assume("mr", "max_rto == 60000")); // 60s max
                                                                            // Double but cap at max
    ctx.push_obligation(ProofObligation::assume(
        "ra_def",
        "rto_after == if rto_before * 2 < max_rto { rto_before * 2 } else { max_rto }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2000", "rto_after == 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RTO: 1000ms → 2000ms (doubled)");
}

#[test]
fn duplicate_ack_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["dup_acks", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fast_retransmit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("da", "dup_acks == 3"));
    ctx.push_obligation(ProofObligation::assume("t", "threshold == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "fr_def",
        "fast_retransmit == if dup_acks >= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "retransmit",
        "fast_retransmit == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 dup ACKs >= 3 threshold → fast retransmit");
}

#[test]
fn bandwidth_delay_product() {
    let mut ctx = VerificationContext::new();
    for v in &["bandwidth_kbps", "rtt_ms", "bdp_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("b", "bandwidth_kbps == 1000")); // 1 Mbps
    ctx.push_obligation(ProofObligation::assume("r", "rtt_ms == 100")); // 100ms
                                                                        // BDP = bandwidth * RTT / 8 (bits to bytes)
    ctx.push_obligation(ProofObligation::assume(
        "bdp_def",
        "bdp_bytes == bandwidth_kbps * rtt_ms / 8",
    ));
    ctx.push_obligation(ProofObligation::assert("is_12500", "bdp_bytes == 12500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "BDP: 1000kbps * 100ms / 8 = 12500 bytes");
}

#[test]
fn cwnd_minimum_one_mss() {
    let mut ctx = VerificationContext::new();
    for v in &["cwnd", "mss"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "cwnd == 1460")); // 1 MSS
    ctx.push_obligation(ProofObligation::assume("m", "mss == 1460"));
    ctx.push_obligation(ProofObligation::assert("at_least_one", "cwnd >= mss"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cwnd 1460 >= 1 MSS (1460)");
}
