// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn station_number() {
    let mut ctx = VerificationContext::new();
    for v in &["station", "max_station"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stn_ok", i32_ty());
    // CC-Link IE station number: 1-120
    ctx.push_obligation(ProofObligation::assume("s", "station == 64"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_station == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stn_ok == if station >= 1 && station <= max_station { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stn_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CC-Link IE: station 64 in [1, 120] → OK");
}

#[test]
fn link_speed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_gbps", u32_ty());
    ctx.declare_var_typed("valid_speed", i32_ty());
    // CC-Link IE: 1 Gbps (standard) or 100 Mbps (field)
    ctx.push_obligation(ProofObligation::assume("sg", "speed_gbps == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_speed == if speed_gbps == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_speed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CC-Link IE: 1 Gbps is valid link speed");
}

#[test]
fn cyclic_data_size() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bytes", "max_data_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("data_ok", i32_ty());
    // Cyclic data per station
    ctx.push_obligation(ProofObligation::assume("db", "data_bytes == 512"));
    ctx.push_obligation(ProofObligation::assume("md", "max_data_bytes == 8192"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "data_ok == if data_bytes <= max_data_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "data_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CC-Link IE: 512 bytes cyclic ≤ 8192 max → OK");
}

#[test]
fn token_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_us", "max_cycle_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cyc_ok", i32_ty());
    // Token rotation cycle time
    ctx.push_obligation(ProofObligation::assume("cu", "cycle_us == 500"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cycle_us == 10000")); // 10ms
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cyc_ok == if cycle_us <= max_cycle_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cyc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CC-Link IE: 500μs cycle ≤ 10ms max → OK");
}

#[test]
fn transient_data() {
    let mut ctx = VerificationContext::new();
    for v in &["trans_bytes", "max_trans_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("trans_ok", i32_ty());
    // Transient (non-cyclic) message size
    ctx.push_obligation(ProofObligation::assume("tb", "trans_bytes == 960"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_trans_bytes == 1920"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "trans_ok == if trans_bytes <= max_trans_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "trans_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CC-Link IE: 960 transient bytes ≤ 1920 max → OK");
}

#[test]
fn network_number() {
    let mut ctx = VerificationContext::new();
    for v in &["net_num", "max_net_num"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("net_ok", i32_ty());
    // Network number: 1-239
    ctx.push_obligation(ProofObligation::assume("nn", "net_num == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "max_net_num == 239"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "net_ok == if net_num >= 1 && net_num <= max_net_num { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "net_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CC-Link IE: network 10 in [1, 239] → OK");
}

#[test]
fn redundancy_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // 1=single, 2=ring redundancy, 3=star redundancy
    ctx.push_obligation(ProofObligation::assume("m", "mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CC-Link IE: ring redundancy is valid mode");
}

#[test]
fn switchover_time() {
    let mut ctx = VerificationContext::new();
    for v in &["switchover_ms", "max_switchover_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sw_ok", i32_ty());
    // Redundancy switchover time
    ctx.push_obligation(ProofObligation::assume("sm", "switchover_ms == 50"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_switchover_ms == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sw_ok == if switchover_ms <= max_switchover_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CC-Link IE: 50ms switchover ≤ 200ms max → OK");
}

#[test]
fn parameter_size() {
    let mut ctx = VerificationContext::new();
    for v in &["param_bytes", "max_param_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("param_ok", i32_ty());
    // Device parameter area size
    ctx.push_obligation(ProofObligation::assume("pb", "param_bytes == 2048"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_param_bytes == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "param_ok == if param_bytes <= max_param_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "param_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CC-Link IE: 2048 param bytes ≤ 4096 max → OK");
}

#[test]
fn total_stations() {
    let mut ctx = VerificationContext::new();
    for v in &["occupied", "max_occupied"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("occ_ok", i32_ty());
    // Occupied stations (some devices use multiple)
    ctx.push_obligation(ProofObligation::assume("o", "occupied == 4"));
    ctx.push_obligation(ProofObligation::assume("mo", "max_occupied == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "occ_ok == if occupied <= max_occupied { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "occ_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CC-Link IE: 4 occupied stations ≤ 16 max → OK");
}
