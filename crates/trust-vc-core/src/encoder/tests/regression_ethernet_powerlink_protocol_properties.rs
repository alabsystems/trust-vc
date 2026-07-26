// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_epl_cycle_time_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_us", "min_cycle_us", "max_cycle_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // EPL cycle time in microseconds: 200μs to 100ms
    ctx.push_obligation(ProofObligation::assume("cu", "cycle_us == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cycle_us == 200"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cycle_us == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cycle_ok == if cycle_us >= min_cycle_us && cycle_us <= max_cycle_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EPL: 1000μs cycle in [200, 100000] → OK");
}

#[test]
fn test_epl_node_count() {
    let mut ctx = VerificationContext::new();
    for v in &["cn_count", "min_cn", "max_cn"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("count_ok", i32_ty());
    // EPL controlled nodes: 1-240 (node IDs 1-240, 240 = MN)
    ctx.push_obligation(ProofObligation::assume("cc", "cn_count == 20"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cn == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cn == 240"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "count_ok == if cn_count >= min_cn && cn_count <= max_cn { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "count_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EPL: 20 CNs in [1, 240] → OK");
}

#[test]
fn test_epl_data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_mbps", u32_ty());
    // EPL operates exclusively on 100 Mbps Fast Ethernet
    ctx.push_obligation(ProofObligation::assume("rm", "rate_mbps == 100"));
    ctx.push_obligation(ProofObligation::assert("always_100", "rate_mbps == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EPL: data rate is always 100 Mbps");
}

#[test]
fn test_epl_pdo_size() {
    let mut ctx = VerificationContext::new();
    for v in &["pdo_bytes", "min_pdo", "max_pdo"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pdo_ok", i32_ty());
    // EPL process data object: 1-1490 bytes (Ethernet payload limit)
    ctx.push_obligation(ProofObligation::assume("pb", "pdo_bytes == 64"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pdo == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pdo == 1490"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pdo_ok == if pdo_bytes >= min_pdo && pdo_bytes <= max_pdo { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pdo_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EPL: 64-byte PDO in [1, 1490] → OK");
}

#[test]
fn test_epl_nmt_state() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nmt_state", u32_ty());
    ctx.declare_var_typed("valid_nmt", i32_ty());
    // EPL NMT states: 1=initialisation, 2=pre-operational, 3=ready-to-operate, 4=operational, 5=stopped
    ctx.push_obligation(ProofObligation::assume("ns", "nmt_state == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vn_def",
        "valid_nmt == if nmt_state == 1 || nmt_state == 2 || nmt_state == 3 || nmt_state == 4 || nmt_state == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_nmt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EPL: operational (4) is valid NMT state");
}

#[test]
fn test_epl_multiplexing_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mux_mode", u32_ty());
    ctx.declare_var_typed("valid_mux", i32_ty());
    // EPL multiplexing modes: 1=isochronous, 2=asynchronous, 3=multiplexed
    ctx.push_obligation(ProofObligation::assume("mm", "mux_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mux == if mux_mode == 1 || mux_mode == 2 || mux_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mux == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EPL: isochronous (1) is valid multiplexing mode");
}

#[test]
fn test_epl_jitter() {
    let mut ctx = VerificationContext::new();
    for v in &["jitter_ns", "min_jitter", "max_jitter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("jitter_ok", i32_ty());
    // EPL jitter (timing accuracy): 1-10000 ns
    ctx.push_obligation(ProofObligation::assume("jn", "jitter_ns == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_jitter == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_jitter == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "jo_def",
        "jitter_ok == if jitter_ns >= min_jitter && jitter_ns <= max_jitter { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "jitter_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EPL: 100ns jitter in [1, 10000] → OK");
}

#[test]
fn test_epl_sdo_max_segment() {
    let mut ctx = VerificationContext::new();
    for v in &["seg_bytes", "min_seg", "max_seg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("seg_ok", i32_ty());
    // EPL SDO max segment size: 4-65536 bytes
    ctx.push_obligation(ProofObligation::assume("sb", "seg_bytes == 256"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_seg == 4"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_seg == 65536"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "seg_ok == if seg_bytes >= min_seg && seg_bytes <= max_seg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "seg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EPL: 256-byte SDO segment in [4, 65536] → OK");
}

#[test]
fn test_epl_cross_traffic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cross_traffic", i32_ty());
    ctx.declare_var_typed("async_phase_extended", i32_ty());
    // EPL cross-traffic flag: 1=cross-traffic present during async phase, 0=none
    ctx.push_obligation(ProofObligation::assume("ct", "cross_traffic == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ape_def",
        "async_phase_extended == if cross_traffic == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "async_phase_extended == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EPL: cross-traffic present → async phase extended");
}

#[test]
fn test_epl_redundancy_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("red_mode", u32_ty());
    ctx.declare_var_typed("valid_red", i32_ty());
    // EPL redundancy modes: 1=none, 2=media redundancy, 3=controller redundancy
    ctx.push_obligation(ProofObligation::assume("rm", "red_mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_red == if red_mode == 1 || red_mode == 2 || red_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_red == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EPL: media redundancy (2) is valid redundancy mode",
    );
}
