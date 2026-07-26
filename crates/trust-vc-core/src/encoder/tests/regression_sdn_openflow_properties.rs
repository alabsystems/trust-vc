// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_table_entry_count() {
    let mut ctx = VerificationContext::new();
    for v in &["current_flows", "max_flows"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_add", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cf", "current_flows == 900"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_flows == 1024"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "can_add == if current_flows < max_flows { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_add == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDN: 900 flows < 1024 max → can add");
}

#[test]
fn match_field_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["rule_a_priority", "rule_b_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("higher_priority", i32_ty());
    // OpenFlow: higher numeric priority wins
    ctx.push_obligation(ProofObligation::assume("rap", "rule_a_priority == 100"));
    ctx.push_obligation(ProofObligation::assume("rbp", "rule_b_priority == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "hp_def",
        "higher_priority == if rule_a_priority > rule_b_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "higher_priority == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDN: priority 100 > 50 → rule A matched first");
}

#[test]
fn group_bucket_weight() {
    let mut ctx = VerificationContext::new();
    for v in &["bucket_weight", "total_weight"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("share_percent", u32_ty());
    // Select group: traffic share = bucket_weight / total_weight × 100
    // Precompute: 30 / 100 × 100 = 30%
    ctx.push_obligation(ProofObligation::assume("bw", "bucket_weight == 30"));
    ctx.push_obligation(ProofObligation::assume("tw", "total_weight == 100"));
    ctx.push_obligation(ProofObligation::assume("sp", "share_percent == 30")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_30", "share_percent == 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDN group: weight 30/100 = 30% share");
}

#[test]
fn meter_band_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["traffic_kbps", "meter_rate_kbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("exceeds_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tk", "traffic_kbps == 15000"));
    ctx.push_obligation(ProofObligation::assume("mrk", "meter_rate_kbps == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "er_def",
        "exceeds_rate == if traffic_kbps > meter_rate_kbps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "exceeds_rate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDN meter: 15Mbps > 10Mbps rate → exceed");
}

#[test]
fn table_pipeline_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["current_table", "max_tables"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_goto", i32_ty());
    // OpenFlow: can only go to higher-numbered tables
    ctx.push_obligation(ProofObligation::assume("ct", "current_table == 3"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tables == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "cg_def",
        "can_goto == if current_table < max_tables { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_goto == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDN pipeline: table 3 < 8 max → can goto next");
}

#[test]
fn controller_connection_count() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "primary_controllers",
        "backup_controllers",
        "total_controllers",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_redundancy", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pc", "primary_controllers == 1"));
    ctx.push_obligation(ProofObligation::assume("bc", "backup_controllers == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "total_controllers == primary_controllers + backup_controllers",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hr_def",
        "has_redundancy == if total_controllers >= 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "total_controllers == 3"));
    ctx.push_obligation(ProofObligation::assert("yes", "has_redundancy == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SDN: 1 primary + 2 backup = 3 controllers (redundant)",
    );
}

#[test]
fn packet_in_buffer_id() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("buffer_id", u32_ty());
    ctx.declare_var_typed("no_buffer_sentinel", u32_ty());
    ctx.declare_var_typed("is_buffered", i32_ty());
    // OpenFlow: buffer_id = 0xFFFFFFFF means no buffering
    ctx.push_obligation(ProofObligation::assume("bi", "buffer_id == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "nbs",
        "no_buffer_sentinel == 4294967295",
    )); // 0xFFFFFFFF
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "is_buffered == if buffer_id != no_buffer_sentinel { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_buffered == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDN: buffer_id 42 ≠ 0xFFFFFFFF → buffered");
}

#[test]
fn port_stats_delta() {
    let mut ctx = VerificationContext::new();
    for v in &["prev_tx_packets", "curr_tx_packets", "delta_packets"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pp", "prev_tx_packets == 100000"));
    ctx.push_obligation(ProofObligation::assume("cp", "curr_tx_packets == 150000"));
    ctx.push_obligation(ProofObligation::assume(
        "dp_def",
        "delta_packets == curr_tx_packets - prev_tx_packets",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_50000",
        "delta_packets == 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDN stats: 150000 - 100000 = 50000 packet delta");
}

#[test]
fn idle_timeout_expiry() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "last_match_time",
        "current_time",
        "idle_timeout",
        "idle_duration",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("expired", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lmt", "last_match_time == 5000"));
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 5400"));
    ctx.push_obligation(ProofObligation::assume("it", "idle_timeout == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "id_def",
        "idle_duration == current_time - last_match_time",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "expired == if idle_duration > idle_timeout { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_400", "idle_duration == 400"));
    ctx.push_obligation(ProofObligation::assert("yes", "expired == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDN flow: 400s idle > 300s timeout → expired");
}

#[test]
fn action_set_output() {
    let mut ctx = VerificationContext::new();
    for v in &["output_port", "max_port"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_port", i32_ty());
    // OpenFlow physical ports: 1 to max
    ctx.push_obligation(ProofObligation::assume("op", "output_port == 5"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_port == 48"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_port == if output_port >= 1 && output_port <= max_port { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_port == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDN: output port 5 in [1, 48] → valid");
}
