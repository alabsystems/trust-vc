// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn modbus_rtu_crc_length() {
    let mut ctx = VerificationContext::new();
    for v in &["pdu_bytes", "crc_bytes", "adu_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Modbus RTU: ADU = address(1) + PDU + CRC(2)
    ctx.push_obligation(ProofObligation::assume("pb", "pdu_bytes == 6"));
    ctx.push_obligation(ProofObligation::assume("cb", "crc_bytes == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ab_def",
        "adu_bytes == 1 + pdu_bytes + crc_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_9", "adu_bytes == 9")); // 1+6+2
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus RTU: 1 + 6 + 2 = 9 byte ADU");
}

#[test]
fn modbus_register_address() {
    let mut ctx = VerificationContext::new();
    for v in &["start_register", "num_registers", "end_register"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "start_register == 100"));
    ctx.push_obligation(ProofObligation::assume("nr", "num_registers == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "er_def",
        "end_register == start_register + num_registers",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_range == if end_register <= 65536 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_110", "end_register == 110"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus: registers [100, 110) within 65536 limit");
}

#[test]
fn rs485_turnaround_time() {
    let mut ctx = VerificationContext::new();
    for v in &["baud_rate", "char_time_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("turnaround_us", u32_ty());
    // Modbus RTU: 3.5 character silence between frames
    // At 9600 baud: 1 char = 11 bits → ~1146us. 3.5 chars ≈ 4010us
    // Precompute since it involves division
    ctx.push_obligation(ProofObligation::assume("br", "baud_rate == 9600"));
    ctx.push_obligation(ProofObligation::assume("ct", "char_time_us == 1146")); // precomputed
    ctx.push_obligation(ProofObligation::assume("tu", "turnaround_us == 4010")); // 3.5 × 1146
    ctx.push_obligation(ProofObligation::assert("is_4010", "turnaround_us == 4010"));
    ctx.push_obligation(ProofObligation::assert("above_1ms", "turnaround_us > 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS485: 3.5 chars @ 9600 baud ≈ 4010us");
}

#[test]
fn lin_break_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["low_bits", "break_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_break", i32_ty());
    // LIN break: >= 13 consecutive dominant bits
    ctx.push_obligation(ProofObligation::assume("lb", "low_bits == 15"));
    ctx.push_obligation(ProofObligation::assume("bt", "break_threshold == 13"));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "is_break == if low_bits >= break_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_break == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIN: 15 >= 13 dominant bits → break detected");
}

#[test]
fn lin_frame_id_parity() {
    let mut ctx = VerificationContext::new();
    for v in &["frame_id", "id_with_parity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("id_valid", i32_ty());
    // LIN: 6-bit ID (0-63), 2 parity bits in upper bits
    ctx.push_obligation(ProofObligation::assume("fi", "frame_id == 42"));
    ctx.push_obligation(ProofObligation::assume("iwp", "id_with_parity == 170")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "id_valid == if frame_id < 64 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "id_valid == 1")); // 42 < 64
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIN: ID 42 < 64 → valid frame ID");
}

#[test]
fn onewire_timing() {
    let mut ctx = VerificationContext::new();
    for v in &["reset_pulse_us", "presence_detect_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timing_ok", i32_ty());
    // 1-Wire: reset pulse >= 480us, presence detect in 15-60us
    ctx.push_obligation(ProofObligation::assume("rp", "reset_pulse_us == 500"));
    ctx.push_obligation(ProofObligation::assume("pd", "presence_detect_us == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timing_ok == if reset_pulse_us >= 480 && presence_detect_us >= 15 && presence_detect_us <= 60 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "timing_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1-Wire: reset 500us, presence 30us → timing OK");
}

#[test]
fn mqtt_qos_retry() {
    let mut ctx = VerificationContext::new();
    for v in &["retry_count", "max_retries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_retry", i32_ty());
    // MQTT QoS 1: retry until PUBACK received
    ctx.push_obligation(ProofObligation::assume("rc", "retry_count == 2"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_retries == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "sr_def",
        "should_retry == if retry_count < max_retries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "should_retry == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MQTT QoS1: retry 2 < 5 max → retry");
}

#[test]
fn coap_message_id() {
    let mut ctx = VerificationContext::new();
    for v in &["current_id", "new_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("id_valid", i32_ty());
    // CoAP: 16-bit message ID, incrementing
    ctx.push_obligation(ProofObligation::assume("ci", "current_id == 65534"));
    ctx.push_obligation(ProofObligation::assume(
        "ni_def",
        "new_id == current_id + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "id_valid == if new_id <= 65535 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_65535", "new_id == 65535"));
    ctx.push_obligation(ProofObligation::assert("ok", "id_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CoAP: msg ID 65534 + 1 = 65535 (still valid)");
}

#[test]
fn bluetooth_connection_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["interval_units", "unit_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("interval_ms", u32_ty());
    ctx.declare_var_typed("valid_interval", i32_ty());
    // BLE: connection interval in 1.25ms units, range 7.5ms-4000ms
    // 80 units × 1.25ms = 100ms. Use precomputed: 80 × 125 / 100 = 100
    ctx.push_obligation(ProofObligation::assume("iu", "interval_units == 80"));
    ctx.push_obligation(ProofObligation::assume("um", "unit_ms == 100")); // precomputed 80×1.25
    ctx.push_obligation(ProofObligation::assume("im", "interval_ms == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "vi_def",
        "valid_interval == if interval_ms >= 7 && interval_ms <= 4000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_100", "interval_ms == 100"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_interval == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BLE: 80 units = 100ms interval (valid)");
}

#[test]
fn zigbee_network_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["max_depth", "current_depth", "max_children"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_add_child", i32_ty());
    ctx.push_obligation(ProofObligation::assume("md", "max_depth == 5"));
    ctx.push_obligation(ProofObligation::assume("cd", "current_depth == 3"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_children == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "cac_def",
        "can_add_child == if current_depth < max_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_add_child == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Zigbee: depth 3 < 5 max → can add child");
}
