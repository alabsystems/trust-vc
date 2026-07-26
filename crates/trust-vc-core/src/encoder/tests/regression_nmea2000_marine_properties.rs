// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_kbps", u32_ty());
    // NMEA 2000 operates at a fixed 250 kbps CAN bus rate
    ctx.push_obligation(ProofObligation::assume("rate_val", "rate_kbps == 250"));
    ctx.push_obligation(ProofObligation::assert("fixed_rate", "rate_kbps == 250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA 2000: fixed CAN bus rate is 250 kbps");
}

#[test]
fn network_devices() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("devices", u32_ty());
    ctx.declare_var_typed("devices_ok", i32_ty());
    // NMEA 2000: max 50 devices on backbone, valid range 1-252
    ctx.push_obligation(ProofObligation::assume("dev_val", "devices == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "dev_ok_def",
        "devices_ok == if devices >= 1 && devices <= 252 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid_devices", "devices_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA 2000: 50 devices in [1, 252] range");
}

#[test]
fn backbone_length() {
    let mut ctx = VerificationContext::new();
    for v in &["length_m", "max_length_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("length_ok", i32_ty());
    // NMEA 2000: max backbone length 100m, absolute max 200m
    ctx.push_obligation(ProofObligation::assume("len_val", "length_m == 100"));
    ctx.push_obligation(ProofObligation::assume("max_val", "max_length_m == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "len_ok_def",
        "length_ok == if length_m <= max_length_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid_length", "length_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA 2000: 100m backbone <= 200m max");
}

#[test]
fn drop_cable_length() {
    let mut ctx = VerificationContext::new();
    for v in &["drop_m", "max_drop_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("drop_ok", i32_ty());
    // NMEA 2000: max drop cable 3m, absolute max 6m
    ctx.push_obligation(ProofObligation::assume("drop_val", "drop_m == 3"));
    ctx.push_obligation(ProofObligation::assume("max_drop_val", "max_drop_m == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "drop_ok_def",
        "drop_ok == if drop_m <= max_drop_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid_drop", "drop_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA 2000: 3m drop cable <= 6m max");
}

#[test]
fn pgn_priority() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("priority", u32_ty());
    ctx.declare_var_typed("priority_ok", i32_ty());
    // NMEA 2000: PGN priority is 3-bit field (0-7), value 3 is typical
    ctx.push_obligation(ProofObligation::assume("pri_val", "priority == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "pri_ok_def",
        "priority_ok == if priority >= 0 && priority <= 7 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_priority",
        "priority_ok == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA 2000: priority 3 in [0, 7] (3-bit field)");
}

#[test]
fn device_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("class", u32_ty());
    ctx.declare_var_typed("valid_class", i32_ty());
    // NMEA 2000 device classes: 25=navigation, 30=electrical, 40=propulsion,
    // 60=communication, 75=sensor, 85=gateway
    ctx.push_obligation(ProofObligation::assume("cls_val", "class == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_class == if class == 25 || class == 30 || class == 40 || class == 60 || class == 75 || class == 85 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_class == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "NMEA 2000: class 25 (navigation) is valid device class",
    );
}

#[test]
fn source_address() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("src_addr", u32_ty());
    ctx.declare_var_typed("addr_ok", i32_ty());
    // NMEA 2000: source address is 8-bit, 0-251 usable (252-255 reserved)
    ctx.push_obligation(ProofObligation::assume("addr_val", "src_addr == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "addr_ok_def",
        "addr_ok == if src_addr >= 0 && src_addr <= 251 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid_addr", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA 2000: source address 100 in [0, 251]");
}

#[test]
fn fast_packet_frames() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frames", u32_ty());
    ctx.declare_var_typed("frames_ok", i32_ty());
    // NMEA 2000: fast-packet protocol uses 1-32 frames
    ctx.push_obligation(ProofObligation::assume("frm_val", "frames == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "frm_ok_def",
        "frames_ok == if frames >= 1 && frames <= 32 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid_frames", "frames_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA 2000: 5 fast-packet frames in [1, 32]");
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_mv", u32_ty());
    ctx.declare_var_typed("voltage_ok", i32_ty());
    // NMEA 2000: bus power 9-16V (9000-16000 mV), nominal 12V
    ctx.push_obligation(ProofObligation::assume("v_val", "voltage_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume(
        "v_ok_def",
        "voltage_ok == if voltage_mv >= 9000 && voltage_mv <= 16000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid_voltage", "voltage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA 2000: 12000 mV (12V) in [9000, 16000] range");
}

#[test]
fn message_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("msg_per_sec", u32_ty());
    ctx.declare_var_typed("rate_ok", i32_ty());
    // NMEA 2000: max transmit rate 1-1000 messages/sec, typical 100
    ctx.push_obligation(ProofObligation::assume("mr_val", "msg_per_sec == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "mr_ok_def",
        "rate_ok == if msg_per_sec >= 1 && msg_per_sec <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid_rate", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NMEA 2000: 100 msg/sec in [1, 1000] range");
}
