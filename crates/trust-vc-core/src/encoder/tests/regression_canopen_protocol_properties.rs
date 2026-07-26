// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn node_id() {
    let mut ctx = VerificationContext::new();
    for v in &["node_id", "max_node_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("nid_ok", i32_ty());
    // CANopen node ID: 1-127
    ctx.push_obligation(ProofObligation::assume("ni", "node_id == 42"));
    ctx.push_obligation(ProofObligation::assume("mn", "max_node_id == 127"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "nid_ok == if node_id >= 1 && node_id <= max_node_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "nid_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen: node 42 in [1, 127] → OK");
}

#[test]
fn pdo_mapping() {
    let mut ctx = VerificationContext::new();
    for v in &["pdo_bytes", "max_pdo_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pdo_ok", i32_ty());
    // PDO data length: max 8 bytes per CAN frame
    ctx.push_obligation(ProofObligation::assume("pb", "pdo_bytes == 6"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pdo_bytes == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pdo_ok == if pdo_bytes <= max_pdo_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pdo_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen: 6-byte PDO ≤ 8 max → OK");
}

#[test]
fn heartbeat_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["hb_ms", "min_hb_ms", "max_hb_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hb_ok", i32_ty());
    // NMT heartbeat producer time
    ctx.push_obligation(ProofObligation::assume("hm", "hb_ms == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_hb_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_hb_ms == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hb_ok == if hb_ms >= min_hb_ms && hb_ms <= max_hb_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hb_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen: 500ms heartbeat in [100, 5000] → OK");
}

#[test]
fn nmt_state() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("state", u32_ty());
    ctx.declare_var_typed("valid_state", i32_ty());
    // NMT states: 0=init, 4=stopped, 5=operational, 127=pre-operational
    ctx.push_obligation(ProofObligation::assume("s", "state == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_state == if state == 0 || state == 4 || state == 5 || state == 127 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_state == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen: operational is valid NMT state");
}

#[test]
fn sdo_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["timeout_ms", "min_timeout_ms", "max_timeout_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sdo_ok", i32_ty());
    // SDO client timeout
    ctx.push_obligation(ProofObligation::assume("tm", "timeout_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_timeout_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_timeout_ms == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sdo_ok == if timeout_ms >= min_timeout_ms && timeout_ms <= max_timeout_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sdo_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen: 1000ms SDO timeout in [100, 10000] → OK");
}

#[test]
fn sync_period() {
    let mut ctx = VerificationContext::new();
    for v in &["sync_us", "min_sync_us", "max_sync_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sync_ok", i32_ty());
    // SYNC message period in microseconds
    ctx.push_obligation(ProofObligation::assume("su", "sync_us == 10000")); // 10ms
    ctx.push_obligation(ProofObligation::assume("mn", "min_sync_us == 1000")); // 1ms
    ctx.push_obligation(ProofObligation::assume("mx", "max_sync_us == 100000")); // 100ms
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sync_ok == if sync_us >= min_sync_us && sync_us <= max_sync_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sync_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen: 10ms SYNC period in [1, 100] ms → OK");
}

#[test]
fn emcy_error_code() {
    let mut ctx = VerificationContext::new();
    for v in &["error_code", "max_error_code"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("err_ok", i32_ty());
    // Emergency error code (16-bit field)
    ctx.push_obligation(ProofObligation::assume("ec", "error_code == 8130")); // 0x1FBE
    ctx.push_obligation(ProofObligation::assume("me", "max_error_code == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "err_ok == if error_code <= max_error_code { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "err_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen: error code 8130 ≤ 65535 (16-bit) → OK");
}

#[test]
fn object_dictionary_index() {
    let mut ctx = VerificationContext::new();
    for v in &["od_index", "min_user_index", "max_user_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("od_ok", i32_ty());
    // Object dictionary: manufacturer-specific range 0x2000-0x5FFF
    ctx.push_obligation(ProofObligation::assume("oi", "od_index == 8200")); // 0x2008
    ctx.push_obligation(ProofObligation::assume("mn", "min_user_index == 8192")); // 0x2000
    ctx.push_obligation(ProofObligation::assume("mx", "max_user_index == 24575")); // 0x5FFF
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "od_ok == if od_index >= min_user_index && od_index <= max_user_index { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "od_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen: OD index 0x2008 in [0x2000, 0x5FFF] → OK");
}

#[test]
fn baud_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud_kbps", u32_ty());
    ctx.declare_var_typed("valid_baud", i32_ty());
    // CANopen standard baud rates
    ctx.push_obligation(ProofObligation::assume("bk", "baud_kbps == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_baud == if baud_kbps == 10 || baud_kbps == 20 || baud_kbps == 50 || baud_kbps == 125 || baud_kbps == 250 || baud_kbps == 500 || baud_kbps == 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_baud == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen: 500 kbps is valid baud rate");
}

#[test]
fn tpdo_count() {
    let mut ctx = VerificationContext::new();
    for v in &["tpdo_count", "max_tpdo"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tpdo_ok", i32_ty());
    // Number of transmit PDOs (standard: up to 4)
    ctx.push_obligation(ProofObligation::assume("tc", "tpdo_count == 4"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tpdo == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tpdo_ok == if tpdo_count <= max_tpdo { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tpdo_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CANopen: 4 TPDOs ≤ 4 max → OK");
}
