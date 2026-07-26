// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_kbps", u32_ty());
    ctx.declare_var_typed("valid_rate", i32_ty());
    // DeviceNet supports 3 non-sequential data rates: 125, 250, 500 kbps
    ctx.push_obligation(ProofObligation::assume("dr", "rate_kbps == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_rate == if rate_kbps == 125 || rate_kbps == 250 || rate_kbps == 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("da", "valid_rate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DeviceNet: 250 kbps is valid data rate");
}

#[test]
fn node_address() {
    let mut ctx = VerificationContext::new();
    for v in &["mac_id", "min_mac", "max_mac"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("addr_ok", i32_ty());
    // DeviceNet MAC ID range is 0-63
    ctx.push_obligation(ProofObligation::assume("mi", "mac_id == 42"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_mac == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_mac == 63"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "addr_ok == if mac_id >= min_mac && mac_id <= max_mac { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("na", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DeviceNet: MAC ID 42 in [0, 63] range");
}

#[test]
fn network_length() {
    let mut ctx = VerificationContext::new();
    for v in &["length_m", "min_length_m", "max_length_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("length_ok", i32_ty());
    // Network cable length in meters (max 500m at 125 kbps)
    ctx.push_obligation(ProofObligation::assume("lm", "length_m == 300"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_length_m == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_length_m == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "length_ok == if length_m >= min_length_m && length_m <= max_length_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("nl", "length_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DeviceNet: 300m cable length in [1, 500] range");
}

#[test]
fn message_group() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("msg_group", u32_ty());
    ctx.declare_var_typed("valid_group", i32_ty());
    // Message groups: 1=Group 1 master/slave, 2=Group 2 unconnected, 3=Group 3 connected, 4=Group 4 offline
    ctx.push_obligation(ProofObligation::assume("mg", "msg_group == 3")); // connected
    ctx.push_obligation(ProofObligation::assume(
        "vg_def",
        "valid_group == if msg_group == 1 || msg_group == 2 || msg_group == 3 || msg_group == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ma", "valid_group == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DeviceNet: Group 3 connected is valid message group",
    );
}

#[test]
fn device_profile() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("profile", u32_ty());
    ctx.declare_var_typed("valid_profile", i32_ty());
    // Device profiles: 1=generic, 2=AC drive, 3=motor overload, 4=photoelectric, 5=pneumatic valve
    ctx.push_obligation(ProofObligation::assume("dp", "profile == 2")); // AC drive
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_profile == if profile == 1 || profile == 2 || profile == 3 || profile == 4 || profile == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("db", "valid_profile == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DeviceNet: AC drive is valid device profile");
}

#[test]
fn io_connection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn_type", u32_ty());
    ctx.declare_var_typed("valid_conn", i32_ty());
    // I/O connection types: 1=polled, 2=strobed, 3=change-of-state/cyclic
    ctx.push_obligation(ProofObligation::assume("ct", "conn_type == 1")); // polled
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_conn == if conn_type == 1 || conn_type == 2 || conn_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ia", "valid_conn == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DeviceNet: polled is valid I/O connection type");
}

#[test]
fn explicit_message_size() {
    let mut ctx = VerificationContext::new();
    for v in &["msg_bytes", "min_msg_bytes", "max_msg_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("msg_ok", i32_ty());
    // Explicit message size in bytes (1-504)
    ctx.push_obligation(ProofObligation::assume("mb", "msg_bytes == 256"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_msg_bytes == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_msg_bytes == 504"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "msg_ok == if msg_bytes >= min_msg_bytes && msg_bytes <= max_msg_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ea", "msg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DeviceNet: 256 byte message in [1, 504] range");
}

#[test]
fn expected_packet_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["epr_ms", "min_epr_ms", "max_epr_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("epr_ok", i32_ty());
    // Expected Packet Rate in milliseconds (1-65535)
    ctx.push_obligation(ProofObligation::assume("em", "epr_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_epr_ms == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_epr_ms == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "epr_ok == if epr_ms >= min_epr_ms && epr_ms <= max_epr_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pa", "epr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DeviceNet: 100ms EPR in [1, 65535] range");
}

#[test]
fn power_supply() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bus_powered", i32_ty());
    ctx.declare_var_typed("valid_power", i32_ty());
    // Power supply mode: 1=bus-powered, 0=self-powered
    ctx.push_obligation(ProofObligation::assume("bp", "bus_powered == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_power == if bus_powered == 0 || bus_powered == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ps", "valid_power == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DeviceNet: bus-powered is valid power supply mode");
}

#[test]
fn fragmentation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frag_type", u32_ty());
    ctx.declare_var_typed("valid_frag", i32_ty());
    // Fragmentation types: 1=no fragmentation, 2=consumed fragment, 3=produced fragment
    ctx.push_obligation(ProofObligation::assume("ft", "frag_type == 2")); // consumed fragment
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_frag == if frag_type == 1 || frag_type == 2 || frag_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fa", "valid_frag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DeviceNet: consumed fragment is valid fragmentation type",
    );
}
