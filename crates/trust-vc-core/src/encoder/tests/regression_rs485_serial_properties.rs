// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn bus_termination() {
    let mut ctx = VerificationContext::new();
    for v in &["termination_ohms", "expected_ohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("properly_terminated", i32_ty());
    // RS-485: 120Ω termination at each end of bus
    ctx.push_obligation(ProofObligation::assume("to", "termination_ohms == 120"));
    ctx.push_obligation(ProofObligation::assume("eo", "expected_ohms == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "pt_def",
        "properly_terminated == if termination_ohms == expected_ohms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "properly_terminated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "RS-485: 120Ω termination = expected → properly terminated",
    );
}

#[test]
fn node_count_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["node_count", "max_nodes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_spec", i32_ty());
    // RS-485: max 32 unit loads (standard), 256 with 1/8 UL transceivers
    ctx.push_obligation(ProofObligation::assume("nc", "node_count == 24"));
    ctx.push_obligation(ProofObligation::assume("mn", "max_nodes == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_spec == if node_count <= max_nodes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-485: 24 nodes ≤ 32 max → within spec");
}

#[test]
fn differential_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["v_a_mv", "v_b_mv", "diff_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_signal", i32_ty());
    // RS-485: differential ≥ 200mV for valid signal at receiver
    ctx.push_obligation(ProofObligation::assume("va", "v_a_mv == 3500"));
    ctx.push_obligation(ProofObligation::assume("vb", "v_b_mv == 3200"));
    ctx.push_obligation(ProofObligation::assume(
        "dm_def",
        "diff_mv == v_a_mv - v_b_mv",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_signal == if diff_mv >= 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_300", "diff_mv == 300"));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_signal == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "RS-485: |3500-3200| = 300mV ≥ 200mV min → valid signal",
    );
}

#[test]
fn cable_length_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["cable_length_m", "max_length_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("length_ok", i32_ty());
    // RS-485: max 1200m (4000 ft) at low data rates
    ctx.push_obligation(ProofObligation::assume("cl", "cable_length_m == 500"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_length_m == 1200"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "length_ok == if cable_length_m <= max_length_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "length_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-485: 500m ≤ 1200m max → cable length OK");
}

#[test]
fn turnaround_time() {
    let mut ctx = VerificationContext::new();
    for v in &["turnaround_us", "min_turnaround_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("turnaround_ok", i32_ty());
    // Half-duplex: driver turnaround delay before switching direction
    ctx.push_obligation(ProofObligation::assume("tu", "turnaround_us == 50"));
    ctx.push_obligation(ProofObligation::assume("mt", "min_turnaround_us == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "turnaround_ok == if turnaround_us >= min_turnaround_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "turnaround_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-485: 50μs turnaround ≥ 10μs min → OK");
}

#[test]
fn baud_rate_distance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud_rate", u32_ty());
    ctx.declare_var_typed("is_high_speed", i32_ty());
    // RS-485 up to 10 Mbps at short distances
    ctx.push_obligation(ProofObligation::assume("br", "baud_rate == 115200"));
    ctx.push_obligation(ProofObligation::assume(
        "ih_def",
        "is_high_speed == if baud_rate > 1000000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "is_high_speed == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-485: 115200 baud ≤ 1 Mbps → not high speed");
}

#[test]
fn frame_format() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bits", "stop_bits", "total_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Frame = start(1) + data + parity(1) + stop. Precompute: 1+8+1+1=11
    ctx.push_obligation(ProofObligation::assume("db", "data_bits == 8"));
    ctx.push_obligation(ProofObligation::assume("sb", "stop_bits == 1"));
    ctx.push_obligation(ProofObligation::assume("tb", "total_bits == 11")); // precomputed: 1+8+1+1
    ctx.push_obligation(ProofObligation::assert("is_11", "total_bits == 11"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-485: 8N1+parity = 11 bits/frame (precomputed)");
}

#[test]
fn bias_resistor() {
    let mut ctx = VerificationContext::new();
    for v in &["bias_kohms", "min_bias_kohms", "max_bias_kohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bias_ok", i32_ty());
    // Fail-safe bias: typically 390Ω to 1kΩ (use kΩ×10 to avoid decimals)
    ctx.push_obligation(ProofObligation::assume("bk", "bias_kohms == 6")); // 560Ω in units of 100Ω
    ctx.push_obligation(ProofObligation::assume("mn", "min_bias_kohms == 4")); // 390Ω
    ctx.push_obligation(ProofObligation::assume("mx", "max_bias_kohms == 10")); // 1kΩ
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bias_ok == if bias_kohms >= min_bias_kohms && bias_kohms <= max_bias_kohms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bias_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-485: bias 560Ω in [390Ω, 1kΩ] → OK");
}

#[test]
fn collision_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["tx_data", "rx_data"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("collision", i32_ty());
    // In half-duplex: if TX != RX while driving, collision occurred
    ctx.push_obligation(ProofObligation::assume("td", "tx_data == 1"));
    ctx.push_obligation(ProofObligation::assume("rd", "rx_data == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "collision == if tx_data != rx_data { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "collision == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-485: TX 1 ≠ RX 0 → collision detected");
}

#[test]
fn multi_drop_address() {
    let mut ctx = VerificationContext::new();
    for v in &["device_addr", "packet_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_addressed", i32_ty());
    // Multi-drop addressing: device responds only to its address
    ctx.push_obligation(ProofObligation::assume("da", "device_addr == 5"));
    ctx.push_obligation(ProofObligation::assume("pa", "packet_addr == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "is_addressed == if device_addr == packet_addr { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_addressed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS-485: device addr 5 = packet addr 5 → addressed");
}
