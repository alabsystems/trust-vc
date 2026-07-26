// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn advertising_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["interval_ms", "min_interval_ms", "max_interval_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_interval", i32_ty());
    // BLE advertising interval: 20ms to 10240ms
    ctx.push_obligation(ProofObligation::assume("im", "interval_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_interval_ms == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_interval_ms == 10240"));
    ctx.push_obligation(ProofObligation::assume(
        "vi_def",
        "valid_interval == if interval_ms >= min_interval_ms && interval_ms <= max_interval_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_interval == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BLE: 100ms in [20, 10240] → valid advertising interval",
    );
}

#[test]
fn connection_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["conn_interval_units", "min_units", "max_units"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_conn", i32_ty());
    // Connection interval: 7.5ms to 4000ms in 1.25ms units (6 to 3200)
    ctx.push_obligation(ProofObligation::assume("ci", "conn_interval_units == 24")); // 30ms
    ctx.push_obligation(ProofObligation::assume("mn", "min_units == 6"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_units == 3200"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_conn == if conn_interval_units >= min_units && conn_interval_units <= max_units { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_conn == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BLE: 24 units in [6, 3200] → valid connection interval",
    );
}

#[test]
fn mtu_size() {
    let mut ctx = VerificationContext::new();
    for v in &["negotiated_mtu", "min_mtu"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mtu_ok", i32_ty());
    // BLE minimum ATT MTU is 23 bytes
    ctx.push_obligation(ProofObligation::assume("nm", "negotiated_mtu == 247"));
    ctx.push_obligation(ProofObligation::assume("mm", "min_mtu == 23"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mtu_ok == if negotiated_mtu >= min_mtu { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mtu_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLE: MTU 247 ≥ 23 minimum → OK");
}

#[test]
fn channel_map_count() {
    let mut ctx = VerificationContext::new();
    for v in &["used_channels", "min_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("map_valid", i32_ty());
    // BLE uses 37 data channels, minimum 2 must be active
    ctx.push_obligation(ProofObligation::assume("uc", "used_channels == 37"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_channels == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "mv_def",
        "map_valid == if used_channels >= min_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "map_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLE: 37 channels ≥ 2 minimum → valid channel map");
}

#[test]
fn tx_power_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tx_power_dbm", u32_ty());
    ctx.declare_var_typed("max_power_dbm", u32_ty());
    ctx.declare_var_typed("within_limit", i32_ty());
    // BLE max TX power: typically +20 dBm (stored as offset from -127)
    // Using unsigned: 0 = -127dBm, 127 = 0dBm, 147 = +20dBm
    ctx.push_obligation(ProofObligation::assume("tp", "tx_power_dbm == 131")); // +4 dBm
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_dbm == 147")); // +20 dBm
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if tx_power_dbm <= max_power_dbm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLE: TX power +4dBm ≤ +20dBm max → within limit");
}

#[test]
fn supervision_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["timeout_units", "conn_interval_units", "slave_latency"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timeout_valid", i32_ty());
    // Supervision timeout > (1 + latency) × conn_interval × 2
    // Precompute: (1+4) × 24 × 2 = 240. timeout=300 > 240.
    // Use precomputed threshold
    ctx.push_obligation(ProofObligation::assume("tu", "timeout_units == 300"));
    ctx.push_obligation(ProofObligation::assume("ci", "conn_interval_units == 24"));
    ctx.push_obligation(ProofObligation::assume("sl", "slave_latency == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "tv_def",
        "timeout_valid == if timeout_units > 240 { 1 } else { 0 }",
    )); // precomputed threshold
    ctx.push_obligation(ProofObligation::assert("yes", "timeout_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BLE: timeout 300 > 240 threshold → valid supervision timeout",
    );
}

#[test]
fn pairing_io_capability() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("io_cap", u32_ty());
    ctx.declare_var_typed("has_display", i32_ty());
    // IO capabilities: 0=DisplayOnly, 1=DisplayYesNo, 2=KeyboardOnly, 3=NoInputNoOutput, 4=KeyboardDisplay
    ctx.push_obligation(ProofObligation::assume("ic", "io_cap == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "hd_def",
        "has_display == if io_cap == 0 || io_cap == 1 || io_cap == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "has_display == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLE: DisplayYesNo (1) → has display");
}

#[test]
fn rssi_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["rssi_offset", "threshold_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("signal_ok", i32_ty());
    // RSSI stored as offset from -127: val 57 = -70dBm, threshold 47 = -80dBm
    // Higher offset = stronger signal. signal_ok when rssi >= threshold.
    ctx.push_obligation(ProofObligation::assume("ro", "rssi_offset == 57")); // -70 dBm
    ctx.push_obligation(ProofObligation::assume("to", "threshold_offset == 47")); // -80 dBm
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "signal_ok == if rssi_offset >= threshold_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "signal_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLE: RSSI -70dBm ≥ -80dBm threshold → signal OK");
}

#[test]
fn gatt_handle_range() {
    let mut ctx = VerificationContext::new();
    for v in &["handle", "start_handle", "end_handle"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // GATT handles are 16-bit, service defines handle range
    ctx.push_obligation(ProofObligation::assume("h", "handle == 25"));
    ctx.push_obligation(ProofObligation::assume("sh", "start_handle == 20"));
    ctx.push_obligation(ProofObligation::assume("eh", "end_handle == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if handle >= start_handle && handle <= end_handle { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BLE: handle 25 in [20, 30] → in GATT service range",
    );
}

#[test]
fn packet_length() {
    let mut ctx = VerificationContext::new();
    for v in &["payload_bytes", "header_bytes", "total_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("length_ok", i32_ty());
    // BLE 5.x: max payload 251, header 2, max total 257 (with MIC)
    ctx.push_obligation(ProofObligation::assume("pb", "payload_bytes == 200"));
    ctx.push_obligation(ProofObligation::assume("hb", "header_bytes == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bytes == payload_bytes + header_bytes",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "length_ok == if total_bytes <= 257 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_202", "total_bytes == 202"));
    ctx.push_obligation(ProofObligation::assert("yes", "length_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLE: 200 + 2 = 202 ≤ 257 max → length OK");
}
