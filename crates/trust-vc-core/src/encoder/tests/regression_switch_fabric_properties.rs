// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn crossbar_port_count() {
    let mut ctx = VerificationContext::new();
    for v in &["input_ports", "output_ports", "crosspoints"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Crossbar: N×N requires N² crosspoints
    // 8 × 8 = 64
    ctx.push_obligation(ProofObligation::assume("ip", "input_ports == 8"));
    ctx.push_obligation(ProofObligation::assume("op", "output_ports == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "cp_def",
        "crosspoints == input_ports * output_ports",
    ));
    ctx.push_obligation(ProofObligation::assert("is_64", "crosspoints == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "switch: 8×8 crossbar = 64 crosspoints");
}

#[test]
fn vlan_tag_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vlan_id", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // VLAN ID range: 1-4094 (0 = priority tagged, 4095 = reserved)
    ctx.push_obligation(ProofObligation::assume("vi", "vlan_id == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if vlan_id >= 1 && vlan_id <= 4094 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "switch: VLAN 100 in [1, 4094] → valid");
}

#[test]
fn mac_table_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["current_entries", "max_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_learn", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ce", "current_entries == 7500"));
    ctx.push_obligation(ProofObligation::assume("me", "max_entries == 8192"));
    ctx.push_obligation(ProofObligation::assume(
        "cl_def",
        "can_learn == if current_entries < max_entries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_learn == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "switch: MAC table 7500 < 8192 → can learn");
}

#[test]
fn spanning_tree_path_cost() {
    let mut ctx = VerificationContext::new();
    for v in &["link_speed_mbps", "path_cost"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_cost", i32_ty());
    // STP: 1Gbps → cost 4, 100Mbps → cost 19
    ctx.push_obligation(ProofObligation::assume("ls", "link_speed_mbps == 1000"));
    ctx.push_obligation(ProofObligation::assume("pc", "path_cost == 4")); // IEEE standard
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_cost == if path_cost > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "path_cost == 4"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_cost == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "STP: 1Gbps → path cost 4");
}

#[test]
fn qos_queue_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["dscp_value", "queue_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_queue", i32_ty());
    // DSCP 46 (EF) → queue 7 (highest priority)
    ctx.push_obligation(ProofObligation::assume("dv", "dscp_value == 46"));
    ctx.push_obligation(ProofObligation::assume("qi", "queue_index == 7")); // precomputed mapping
    ctx.push_obligation(ProofObligation::assume(
        "vq_def",
        "valid_queue == if queue_index <= 7 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_7", "queue_index == 7"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_queue == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QoS: DSCP 46 (EF) → queue 7 (valid)");
}

#[test]
fn port_bandwidth_utilization() {
    let mut ctx = VerificationContext::new();
    for v in &["ingress_mbps", "egress_mbps", "port_capacity_mbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("congested", i32_ty());
    ctx.push_obligation(ProofObligation::assume("im", "ingress_mbps == 800"));
    ctx.push_obligation(ProofObligation::assume("em", "egress_mbps == 900"));
    ctx.push_obligation(ProofObligation::assume("pcm", "port_capacity_mbps == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "congested == if egress_mbps > port_capacity_mbps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "congested == 0")); // 900 <= 1000
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "switch: 900Mbps egress ≤ 1Gbps capacity → no congestion",
    );
}

#[test]
fn lag_member_distribution() {
    let mut ctx = VerificationContext::new();
    for v in &["total_flows", "lag_members", "flows_per_member"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // LAG: distribute flows across member ports
    // 1000 flows / 4 members = 250 per member
    ctx.push_obligation(ProofObligation::assume("tf", "total_flows == 1000"));
    ctx.push_obligation(ProofObligation::assume("lm", "lag_members == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "fpm_def",
        "flows_per_member == total_flows / lag_members",
    ));
    ctx.push_obligation(ProofObligation::assert("is_250", "flows_per_member == 250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "LAG: 1000 / 4 = 250 flows per member");
}

#[test]
fn acl_tcam_usage() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "used_entries",
        "new_rule_entries",
        "total_entries",
        "tcam_capacity",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ue", "used_entries == 900"));
    ctx.push_obligation(ProofObligation::assume("nre", "new_rule_entries == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "te_def",
        "total_entries == used_entries + new_rule_entries",
    ));
    ctx.push_obligation(ProofObligation::assume("tc", "tcam_capacity == 1024"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fits == if total_entries <= tcam_capacity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_950", "total_entries == 950"));
    ctx.push_obligation(ProofObligation::assert("ok", "fits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "switch TCAM: 900 + 50 = 950 ≤ 1024 capacity");
}

#[test]
fn multicast_group_membership() {
    let mut ctx = VerificationContext::new();
    for v in &["group_members", "max_groups"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("port_in_group", i32_ty());
    ctx.push_obligation(ProofObligation::assume("gm", "group_members == 3")); // ports in group
    ctx.push_obligation(ProofObligation::assume("mg", "max_groups == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "pig_def",
        "port_in_group == if group_members > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "port_in_group == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "switch mcast: 3 members > 0 → group active");
}

#[test]
fn storm_control_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["broadcast_pps", "threshold_pps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("storm_detected", i32_ty());
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
        "switch: 5000 pps > 3000 threshold → broadcast storm",
    );
}
