// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn mac_table_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["entries_used", "max_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("table_full", i32_ty());
    // MAC address table: typical 8K-32K entries
    ctx.push_obligation(ProofObligation::assume("eu", "entries_used == 8000"));
    ctx.push_obligation(ProofObligation::assume("me", "max_entries == 8192"));
    ctx.push_obligation(ProofObligation::assume(
        "tf_def",
        "table_full == if entries_used >= max_entries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "table_full == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Switch: 8000 entries < 8192 max → table not full");
}

#[test]
fn vlan_id_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vlan_id", u32_ty());
    ctx.declare_var_typed("is_valid", i32_ty());
    // VLAN IDs: 1-4094 valid, 0 and 4095 reserved
    ctx.push_obligation(ProofObligation::assume("vi", "vlan_id == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "is_valid == if vlan_id >= 1 && vlan_id <= 4094 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Switch: VLAN 100 in [1, 4094] → valid");
}

#[test]
fn spanning_tree_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["bridge_priority", "other_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_root", i32_ty());
    // STP: lower priority = root bridge. Priority in multiples of 4096.
    ctx.push_obligation(ProofObligation::assume("bp", "bridge_priority == 4096"));
    ctx.push_obligation(ProofObligation::assume("op", "other_priority == 32768")); // default
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_root == if bridge_priority < other_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_root == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Switch: priority 4096 < 32768 → becomes root bridge",
    );
}

#[test]
fn port_speed_negotiation() {
    let mut ctx = VerificationContext::new();
    for v in &["local_speed_mbps", "remote_speed_mbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("negotiated_speed", u32_ty());
    // Auto-negotiation: use minimum of both sides. Precompute: min(1000, 100) = 100
    ctx.push_obligation(ProofObligation::assume("ls", "local_speed_mbps == 1000"));
    ctx.push_obligation(ProofObligation::assume("rs", "remote_speed_mbps == 100"));
    ctx.push_obligation(ProofObligation::assume("ns", "negotiated_speed == 100")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_100", "negotiated_speed == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Switch: min(1000, 100) = 100 Mbps (precomputed)");
}

#[test]
fn queue_depth_check() {
    let mut ctx = VerificationContext::new();
    for v in &["queue_packets", "max_queue"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("queue_full", i32_ty());
    // Per-port output queue depth
    ctx.push_obligation(ProofObligation::assume("qp", "queue_packets == 500"));
    ctx.push_obligation(ProofObligation::assume("mq", "max_queue == 1024"));
    ctx.push_obligation(ProofObligation::assume(
        "qf_def",
        "queue_full == if queue_packets >= max_queue { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "queue_full == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Switch: queue 500 < 1024 max → not full");
}

#[test]
fn cos_to_queue_mapping() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cos_value", u32_ty());
    ctx.declare_var_typed("is_high_priority", i32_ty());
    // 802.1p CoS: 0-7, values 5-7 are high priority
    ctx.push_obligation(ProofObligation::assume("cv", "cos_value == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "ih_def",
        "is_high_priority == if cos_value >= 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_high_priority == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Switch: CoS 6 ≥ 5 → high priority queue");
}

#[test]
fn port_mirroring_bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["mirror_traffic_mbps", "mirror_port_capacity_mbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_mirror", i32_ty());
    // Mirror port must handle combined traffic
    ctx.push_obligation(ProofObligation::assume("mt", "mirror_traffic_mbps == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "mc",
        "mirror_port_capacity_mbps == 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "can_mirror == if mirror_traffic_mbps <= mirror_port_capacity_mbps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_mirror == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Switch: mirror 800 Mbps ≤ 1000 port → can mirror");
}

#[test]
fn aging_timer() {
    let mut ctx = VerificationContext::new();
    for v in &["entry_age_sec", "aging_time_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_age_out", i32_ty());
    // MAC table aging: default 300 seconds
    ctx.push_obligation(ProofObligation::assume("ea", "entry_age_sec == 350"));
    ctx.push_obligation(ProofObligation::assume("at", "aging_time_sec == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "sa_def",
        "should_age_out == if entry_age_sec >= aging_time_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "should_age_out == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Switch: entry 350s ≥ 300s aging → should age out");
}

#[test]
fn trunk_port_count() {
    let mut ctx = VerificationContext::new();
    for v in &["active_links", "min_links"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lag_healthy", i32_ty());
    // Link Aggregation Group: minimum links for operation
    ctx.push_obligation(ProofObligation::assume("al", "active_links == 3"));
    ctx.push_obligation(ProofObligation::assume("ml", "min_links == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "lh_def",
        "lag_healthy == if active_links >= min_links { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "lag_healthy == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Switch: 3 active links ≥ 2 min → LAG healthy");
}

#[test]
fn storm_control_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["broadcast_pps", "threshold_pps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("storm_detected", i32_ty());
    // Storm control: rate-limit broadcast/multicast
    ctx.push_obligation(ProofObligation::assume("bp", "broadcast_pps == 5000"));
    ctx.push_obligation(ProofObligation::assume("tp", "threshold_pps == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "sd_def",
        "storm_detected == if broadcast_pps > threshold_pps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "storm_detected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Switch: 5000 pps > 3000 threshold → broadcast storm",
    );
}
