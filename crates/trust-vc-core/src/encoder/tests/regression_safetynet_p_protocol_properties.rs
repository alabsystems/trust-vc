// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_mbps", u32_ty());
    // SafetyNET p operates at fixed 100 Mbps Ethernet
    ctx.push_obligation(ProofObligation::assume("dr_val", "rate_mbps == 100"));
    ctx.push_obligation(ProofObligation::assert("dr_fixed", "rate_mbps == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "data rate fixed at 100 Mbps");
}

#[test]
fn safety_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sil", u32_ty());
    ctx.declare_var_typed("valid_sil", i32_ty());
    // 1=SIL 1, 2=SIL 2, 3=SIL 3
    ctx.push_obligation(ProofObligation::assume("sl_val", "sil == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "sl_valid_def",
        "valid_sil == if sil == 1 || sil == 2 || sil == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sl_check", "valid_sil == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "safety level 3 (SIL 3) is valid");
}

#[test]
fn node_count() {
    let mut ctx = VerificationContext::new();
    for v in &["nodes", "nodes_min", "nodes_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of nodes on SafetyNET p segment: bounded 1-64
    ctx.push_obligation(ProofObligation::assume("nc_val", "nodes == 32"));
    ctx.push_obligation(ProofObligation::assume("nc_min", "nodes_min == 1"));
    ctx.push_obligation(ProofObligation::assume("nc_max", "nodes_max == 64"));
    ctx.push_obligation(ProofObligation::assert(
        "nc_in_range",
        "nodes >= nodes_min && nodes <= nodes_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "node count 32 in range [1,64]");
}

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_us", "cycle_min", "cycle_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Cycle time in microseconds: bounded 250-100000
    ctx.push_obligation(ProofObligation::assume("ct_val", "cycle_us == 1000"));
    ctx.push_obligation(ProofObligation::assume("ct_min", "cycle_min == 250"));
    ctx.push_obligation(ProofObligation::assume("ct_max", "cycle_max == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "ct_in_range",
        "cycle_us >= cycle_min && cycle_us <= cycle_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cycle time 1000 us in range [250,100000]");
}

#[test]
fn safety_telegram_size() {
    let mut ctx = VerificationContext::new();
    for v in &["telegram_bytes", "tg_min", "tg_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Safety telegram size in bytes: bounded 1-1024
    ctx.push_obligation(ProofObligation::assume("st_val", "telegram_bytes == 128"));
    ctx.push_obligation(ProofObligation::assume("st_min", "tg_min == 1"));
    ctx.push_obligation(ProofObligation::assume("st_max", "tg_max == 1024"));
    ctx.push_obligation(ProofObligation::assert(
        "st_in_range",
        "telegram_bytes >= tg_min && telegram_bytes <= tg_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "safety telegram size 128 bytes in range [1,1024]");
}

#[test]
fn crc_polynomial() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("crc", u32_ty());
    ctx.declare_var_typed("valid_crc", i32_ty());
    // 1=CRC-16, 2=CRC-32, 3=CRC-64
    ctx.push_obligation(ProofObligation::assume("cp_val", "crc == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "cp_valid_def",
        "valid_crc == if crc == 1 || crc == 2 || crc == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cp_check", "valid_crc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CRC polynomial 2 (CRC-32) is valid");
}

#[test]
fn watchdog_time() {
    let mut ctx = VerificationContext::new();
    for v in &["wd_ms", "wd_min", "wd_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Watchdog time in milliseconds: bounded 1-65535
    ctx.push_obligation(ProofObligation::assume("wt_val", "wd_ms == 500"));
    ctx.push_obligation(ProofObligation::assume("wt_min", "wd_min == 1"));
    ctx.push_obligation(ProofObligation::assume("wt_max", "wd_max == 65535"));
    ctx.push_obligation(ProofObligation::assert(
        "wt_in_range",
        "wd_ms >= wd_min && wd_ms <= wd_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "watchdog time 500 ms in range [1,65535]");
}

#[test]
fn topology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("topo", u32_ty());
    ctx.declare_var_typed("valid_topo", i32_ty());
    // 1=star, 2=line, 3=ring
    ctx.push_obligation(ProofObligation::assume("tp_val", "topo == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_valid_def",
        "valid_topo == if topo == 1 || topo == 2 || topo == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tp_check", "valid_topo == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "topology 1 (star) is valid");
}

#[test]
fn redundancy_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("redundancy", i32_ty());
    // Boolean-like flag: 1=none, 0=media redundancy
    ctx.push_obligation(ProofObligation::assume("rm_val", "redundancy == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "rm_is_bool",
        "redundancy == 0 || redundancy == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "redundancy mode 1 (none) is valid boolean");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["resp_us", "resp_min", "resp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Response time in microseconds: bounded 1-50000
    ctx.push_obligation(ProofObligation::assume("rt_val", "resp_us == 5000"));
    ctx.push_obligation(ProofObligation::assume("rt_min", "resp_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rt_max", "resp_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_in_range",
        "resp_us >= resp_min && resp_us <= resp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time 5000 us in range [1,50000]");
}
