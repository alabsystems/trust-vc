// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_port_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ports", "min_ports", "max_ports"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ports_val", "ports == 16"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_ports == 4"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_ports == 48"));
    ctx.push_obligation(ProofObligation::assert(
        "ports_in_range",
        "ports >= min_ports && ports <= max_ports",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Ethernet ports 16 in [4, 48]");
}

#[test]
fn test_speed_four_way_mbps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", u32_ty());
    // 10, 100, 1000, 10000 Mbps (non-sequential)
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_speed",
        "speed == 10 || speed == 100 || speed == 1000 || speed == 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed 1000 Mbps is one of {10, 100, 1000, 10000}");
}

#[test]
fn test_redundancy_protocol_four_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("protocol", u32_ty());
    // 1=RSTP, 2=MRP, 3=HSR, 4=PRP
    ctx.push_obligation(ProofObligation::assume("proto_val", "protocol == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_protocol",
        "protocol == 1 || protocol == 2 || protocol == 3 || protocol == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "redundancy HSR (3) is one of {1=RSTP, 2=MRP, 3=HSR, 4=PRP}",
    );
}

#[test]
fn test_vlan_count() {
    let mut ctx = VerificationContext::new();
    for v in &["vlans", "min_vlans", "max_vlans"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("vlans_val", "vlans == 64"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_vlans == 1"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_vlans == 4096"));
    ctx.push_obligation(ProofObligation::assert(
        "vlans_in_range",
        "vlans >= min_vlans && vlans <= max_vlans",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VLAN count 64 in [1, 4096]");
}

#[test]
fn test_mac_table_size() {
    let mut ctx = VerificationContext::new();
    for v in &["mac_entries", "min_entries", "max_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("mac_val", "mac_entries == 8000"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_entries == 1000"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_entries == 32000"));
    ctx.push_obligation(ProofObligation::assert(
        "mac_in_range",
        "mac_entries >= min_entries && mac_entries <= max_entries",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MAC table 8000 entries in [1000, 32000]");
}

#[test]
fn test_fiber_port_count() {
    let mut ctx = VerificationContext::new();
    for v in &["fiber_ports", "min_fiber", "max_fiber"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fiber_val", "fiber_ports == 2"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_fiber == 0"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_fiber == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "fiber_in_range",
        "fiber_ports >= min_fiber && fiber_ports <= max_fiber",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SFP uplinks 2 in [0, 8]");
}

#[test]
fn test_poe_power_budget_watts() {
    let mut ctx = VerificationContext::new();
    for v in &["poe_budget", "min_poe", "max_poe"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("poe_val", "poe_budget == 240"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_poe == 0"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_poe == 960"));
    ctx.push_obligation(ProofObligation::assert(
        "poe_in_range",
        "poe_budget >= min_poe && poe_budget <= max_poe",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PoE budget 240W in [0, 960]");
}

#[test]
fn test_operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp", "max_temp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Offset +500: actual = value - 500, so 525 = 25C, 460 = -40C, 585 = 85C
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assume("min_val", "min_temp == 460"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_temp == 585"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "temp_offset >= min_temp && temp_offset <= max_temp",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "temp 25C (offset 525) in [460 (-40C), 585 (85C)]");
}

#[test]
fn test_management_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mgmt_type", u32_ty());
    // 1=unmanaged, 2=managed, 3=layer3
    ctx.push_obligation(ProofObligation::assume("mgmt_val", "mgmt_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_mgmt",
        "mgmt_type == 1 || mgmt_type == 2 || mgmt_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "management managed (2) is one of {1=unmanaged, 2=managed, 3=layer3}",
    );
}

#[test]
fn test_ring_recovery_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sub_ms_recovery", i32_ty());
    ctx.declare_var_typed("ring_ready", i32_ty());
    // Boolean flag: 1 = sub-ms ring recovery enabled, 0 = disabled
    ctx.push_obligation(ProofObligation::assume("flag_val", "sub_ms_recovery == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ready_def",
        "ring_ready == if sub_ms_recovery == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ring_ok", "ring_ready == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sub-ms ring recovery enabled => ring ready");
}
