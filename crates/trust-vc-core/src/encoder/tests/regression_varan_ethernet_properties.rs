// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_mbps", u32_ty());
    // VARAN operates at fixed 100 Mbps Ethernet
    ctx.push_obligation(ProofObligation::assume("dr_val", "rate_mbps == 100"));
    ctx.push_obligation(ProofObligation::assert("dr_fixed", "rate_mbps == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "data rate fixed at 100 Mbps");
}

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_us", "cycle_min", "cycle_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Cycle time in microseconds: bounded 62-100000 (min 62.5 us)
    ctx.push_obligation(ProofObligation::assume("ct_val", "cycle_us == 125"));
    ctx.push_obligation(ProofObligation::assume("ct_min", "cycle_min == 62"));
    ctx.push_obligation(ProofObligation::assume("ct_max", "cycle_max == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "ct_in_range",
        "cycle_us >= cycle_min && cycle_us <= cycle_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cycle time 125 us in range [62,100000]");
}

#[test]
fn node_count() {
    let mut ctx = VerificationContext::new();
    for v in &["nodes", "nodes_min", "nodes_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of VARAN nodes per network: bounded 1-254
    ctx.push_obligation(ProofObligation::assume("nc_val", "nodes == 64"));
    ctx.push_obligation(ProofObligation::assume("nc_min", "nodes_min == 1"));
    ctx.push_obligation(ProofObligation::assume("nc_max", "nodes_max == 254"));
    ctx.push_obligation(ProofObligation::assert(
        "nc_in_range",
        "nodes >= nodes_min && nodes <= nodes_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "node count 64 in range [1,254]");
}

#[test]
fn topology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("topo", u32_ty());
    ctx.declare_var_typed("valid_topo", i32_ty());
    // 1=daisy-chain, 2=star, 3=tree
    ctx.push_obligation(ProofObligation::assume("tp_val", "topo == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_valid_def",
        "valid_topo == if topo == 1 || topo == 2 || topo == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tp_check", "valid_topo == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "topology 1 (daisy-chain) is valid");
}

#[test]
fn data_payload() {
    let mut ctx = VerificationContext::new();
    for v in &["payload_bytes", "pl_min", "pl_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Data payload in bytes per frame: bounded 1-1500
    ctx.push_obligation(ProofObligation::assume("dp_val", "payload_bytes == 256"));
    ctx.push_obligation(ProofObligation::assume("dp_min", "pl_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dp_max", "pl_max == 1500"));
    ctx.push_obligation(ProofObligation::assert(
        "dp_in_range",
        "payload_bytes >= pl_min && payload_bytes <= pl_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "data payload 256 bytes in range [1,1500]");
}

#[test]
fn jitter() {
    let mut ctx = VerificationContext::new();
    for v in &["jitter_ns", "jt_min", "jt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Network jitter in nanoseconds: bounded 1-1000
    ctx.push_obligation(ProofObligation::assume("jt_val", "jitter_ns == 50"));
    ctx.push_obligation(ProofObligation::assume("jt_min", "jt_min == 1"));
    ctx.push_obligation(ProofObligation::assume("jt_max", "jt_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "jt_in_range",
        "jitter_ns >= jt_min && jitter_ns <= jt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "jitter 50 ns in range [1,1000]");
}

#[test]
fn hot_plug() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hot_plug", i32_ty());
    // Boolean flag: 1=supported, 0=not supported
    ctx.push_obligation(ProofObligation::assume("hp_val", "hot_plug == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "hp_is_bool",
        "hot_plug == 0 || hot_plug == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hot plug 1 (supported) is valid boolean");
}

#[test]
fn sync_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sync", u32_ty());
    ctx.declare_var_typed("valid_sync", i32_ty());
    // 1=synchronous, 2=asynchronous, 3=mixed
    ctx.push_obligation(ProofObligation::assume("sm_val", "sync == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sm_valid_def",
        "valid_sync == if sync == 1 || sync == 2 || sync == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sm_check", "valid_sync == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sync mode 1 (synchronous) is valid");
}

#[test]
fn cable_length() {
    let mut ctx = VerificationContext::new();
    for v in &["meters", "m_min", "m_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Cable length in meters per segment: bounded 1-100
    ctx.push_obligation(ProofObligation::assume("cl_val", "meters == 50"));
    ctx.push_obligation(ProofObligation::assume("cl_min", "m_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cl_max", "m_max == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "cl_in_range",
        "meters >= m_min && meters <= m_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cable length 50 m in range [1,100]");
}

#[test]
fn error_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("err_detect", u32_ty());
    ctx.declare_var_typed("valid_err", i32_ty());
    // 1=CRC-32, 2=frame check, 3=watchdog
    ctx.push_obligation(ProofObligation::assume("ed_val", "err_detect == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ed_valid_def",
        "valid_err == if err_detect == 1 || err_detect == 2 || err_detect == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ed_check", "valid_err == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "error detection 1 (CRC-32) is valid");
}
