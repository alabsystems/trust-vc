// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pan_id_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pan_id", u32_ty());
    ctx.declare_var_typed("is_valid", i32_ty());
    // Zigbee PAN ID: 0x0000-0x3FFF valid, 0xFFFF = broadcast
    ctx.push_obligation(ProofObligation::assume("pi", "pan_id == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "is_valid == if pan_id <= 16383 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Zigbee: PAN ID 100 ≤ 16383 → valid");
}

#[test]
fn short_address() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("short_addr", u32_ty());
    ctx.declare_var_typed("is_unicast", i32_ty());
    // Short address: 0x0000-0xFFF7 unicast, 0xFFFF broadcast
    ctx.push_obligation(ProofObligation::assume("sa", "short_addr == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "iu_def",
        "is_unicast == if short_addr <= 65527 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_unicast == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Zigbee: addr 1000 ≤ 0xFFF7 → unicast");
}

#[test]
fn max_payload_size() {
    let mut ctx = VerificationContext::new();
    for v in &["payload_bytes", "max_payload"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("size_ok", i32_ty());
    // IEEE 802.15.4: max payload ~100 bytes after headers
    ctx.push_obligation(ProofObligation::assume("pb", "payload_bytes == 80"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_payload == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "size_ok == if payload_bytes <= max_payload { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "size_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Zigbee: 80 bytes ≤ 100 max payload → OK");
}

#[test]
fn network_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["current_depth", "max_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("depth_ok", i32_ty());
    // Zigbee: max network depth typically 5-15 hops
    ctx.push_obligation(ProofObligation::assume("cd", "current_depth == 3"));
    ctx.push_obligation(ProofObligation::assume("md", "max_depth == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "depth_ok == if current_depth <= max_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "depth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Zigbee: depth 3 ≤ 5 max → OK");
}

#[test]
fn routing_table_entry() {
    let mut ctx = VerificationContext::new();
    for v in &["route_entries", "max_routes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("table_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("re", "route_entries == 20"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_routes == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "table_ok == if route_entries <= max_routes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "table_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Zigbee: 20 routes ≤ 40 max → routing table OK");
}

#[test]
fn channel_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channel", u32_ty());
    ctx.declare_var_typed("is_zigbee_channel", i32_ty());
    // Zigbee uses 802.15.4 channels 11-26 (2.4 GHz band)
    ctx.push_obligation(ProofObligation::assume("ch", "channel == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "iz_def",
        "is_zigbee_channel == if channel >= 11 && channel <= 26 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_zigbee_channel == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Zigbee: channel 15 in [11, 26] → valid Zigbee channel",
    );
}

#[test]
fn link_quality() {
    let mut ctx = VerificationContext::new();
    for v in &["lqi", "min_lqi"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("link_ok", i32_ty());
    // LQI: 0-255, higher is better. Minimum for reliable link ~100
    ctx.push_obligation(ProofObligation::assume("l", "lqi == 200"));
    ctx.push_obligation(ProofObligation::assume("ml", "min_lqi == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "link_ok == if lqi >= min_lqi { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "link_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Zigbee: LQI 200 ≥ 100 min → link OK");
}

#[test]
fn coordinator_role() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("device_type", u32_ty());
    ctx.declare_var_typed("is_coordinator", i32_ty());
    // 0=coordinator, 1=router, 2=end device
    ctx.push_obligation(ProofObligation::assume("dt", "device_type == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ic_def",
        "is_coordinator == if device_type == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_coordinator == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Zigbee: device type 0 → coordinator");
}

#[test]
fn security_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sec_level", u32_ty());
    ctx.declare_var_typed("has_encryption", i32_ty());
    // Security levels: 0=none, 1-3=MIC only, 4=ENC, 5-7=ENC+MIC
    ctx.push_obligation(ProofObligation::assume("sl", "sec_level == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "he_def",
        "has_encryption == if sec_level >= 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "has_encryption == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Zigbee: security level 5 ≥ 4 → encrypted");
}

#[test]
fn neighbor_table() {
    let mut ctx = VerificationContext::new();
    for v in &["neighbor_count", "max_neighbors"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_add", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nc", "neighbor_count == 15"));
    ctx.push_obligation(ProofObligation::assume("mn", "max_neighbors == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "can_add == if neighbor_count < max_neighbors { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_add == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Zigbee: 15 neighbors < 20 max → can add more");
}
