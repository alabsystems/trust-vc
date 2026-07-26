// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_us", "min_cycle_us", "max_cycle_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // POWERLINK isochronous cycle time in microseconds
    ctx.push_obligation(ProofObligation::assume("cu", "cycle_us == 400"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cycle_us == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cycle_us == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cycle_ok == if cycle_us >= min_cycle_us && cycle_us <= max_cycle_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 400us cycle in [100, 100000] range");
}

#[test]
fn node_count() {
    let mut ctx = VerificationContext::new();
    for v in &["cn_count", "min_cn", "max_cn"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cn_ok", i32_ty());
    // Controlled Nodes on EPL network: 1-239
    ctx.push_obligation(ProofObligation::assume("cc", "cn_count == 40"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cn == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cn == 239"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cn_ok == if cn_count >= min_cn && cn_count <= max_cn { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cn_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 40 controlled nodes in [1, 239] range");
}

#[test]
fn node_id() {
    let mut ctx = VerificationContext::new();
    for v in &["node_id", "min_id", "max_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("id_ok", i32_ty());
    // Node identifier: 1-239 for CN, 240 for MN
    ctx.push_obligation(ProofObligation::assume("ni", "node_id == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_id == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_id == 240"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "id_ok == if node_id >= min_id && node_id <= max_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "id_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: node ID 10 in [1, 240] range");
}

#[test]
fn payload_size() {
    let mut ctx = VerificationContext::new();
    for v in &["payload_bytes", "min_payload", "max_payload"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("payload_ok", i32_ty());
    // PDO payload in bytes
    ctx.push_obligation(ProofObligation::assume("pb", "payload_bytes == 256"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_payload == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_payload == 1490"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "payload_ok == if payload_bytes >= min_payload && payload_bytes <= max_payload { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "payload_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "POWERLINK: 256-byte PDO payload in [1, 1490] range",
    );
}

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_mbps", u32_ty());
    // POWERLINK operates at fixed 100 Mbps Fast Ethernet
    ctx.push_obligation(ProofObligation::assume("rm", "rate_mbps == 100"));
    ctx.push_obligation(ProofObligation::assert("fixed_rate", "rate_mbps == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: fixed 100 Mbps Ethernet data rate");
}

#[test]
fn nmt_state() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nmt", u32_ty());
    ctx.declare_var_typed("valid_nmt", i32_ty());
    // NMT states: 1=off, 2=initialisation, 28=pre-operational, 29=ready-to-operate, 30=operational
    ctx.push_obligation(ProofObligation::assume("nm", "nmt == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "vn_def",
        "valid_nmt == if nmt == 1 || nmt == 2 || nmt == 28 || nmt == 29 || nmt == 30 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_nmt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: NMT state 30 (operational) is valid");
}

#[test]
fn multiplexing_slots() {
    let mut ctx = VerificationContext::new();
    for v in &["mux_slots", "min_mux", "max_mux"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mux_ok", i32_ty());
    // Asynchronous multiplexing slot count: 0-254
    ctx.push_obligation(ProofObligation::assume("ms", "mux_slots == 8"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_mux == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_mux == 254"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mux_ok == if mux_slots >= min_mux && mux_slots <= max_mux { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mux_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 8 multiplexing slots in [0, 254] range");
}

#[test]
fn soc_jitter() {
    let mut ctx = VerificationContext::new();
    for v in &["jitter_ns", "max_jitter_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("jitter_ok", i32_ty());
    // Start-of-Cycle jitter in nanoseconds, max 1000ns
    ctx.push_obligation(ProofObligation::assume("jn", "jitter_ns == 100"));
    ctx.push_obligation(ProofObligation::assume("mj", "max_jitter_ns == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "jo_def",
        "jitter_ok == if jitter_ns <= max_jitter_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "jitter_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 100ns SoC jitter within 1000ns max");
}

#[test]
fn pres_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["timeout_us", "max_timeout_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timeout_ok", i32_ty());
    // PRes response timeout in microseconds, max 10000us
    ctx.push_obligation(ProofObligation::assume("tu", "timeout_us == 50"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_timeout_us == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timeout_ok == if timeout_us <= max_timeout_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timeout_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 50us PRes timeout within 10000us max");
}

#[test]
fn network_redundancy() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("redundancy", u32_ty());
    ctx.declare_var_typed("valid_redundancy", i32_ty());
    // Redundancy modes: 1=none, 2=media redundancy (MRP), 3=ring redundancy
    ctx.push_obligation(ProofObligation::assume("rd", "redundancy == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_redundancy == if redundancy == 1 || redundancy == 2 || redundancy == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_redundancy == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: redundancy mode 2 (MRP) is valid");
}
