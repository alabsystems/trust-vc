// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn com_speed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_kbaud", u32_ty());
    ctx.declare_var_typed("is_com3", i32_ty());
    // IO-Link COM modes: COM1=4.8, COM2=38.4, COM3=230.4 kBaud
    ctx.push_obligation(ProofObligation::assume("sk", "speed_kbaud == 230"));
    ctx.push_obligation(ProofObligation::assume(
        "ic_def",
        "is_com3 == if speed_kbaud == 230 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_com3 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IO-Link: 230.4 kBaud → COM3 mode");
}

#[test]
fn process_data_size() {
    let mut ctx = VerificationContext::new();
    for v in &["pd_octets", "max_pd_octets"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("size_ok", i32_ty());
    // Process data: up to 32 octets (IO-Link v1.1)
    ctx.push_obligation(ProofObligation::assume("po", "pd_octets == 8"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pd_octets == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "size_ok == if pd_octets <= max_pd_octets { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "size_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IO-Link: 8 octets ≤ 32 max → PD size OK");
}

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_ms_x10", "min_cycle_ms_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timing_ok", i32_ty());
    // Minimum cycle time: depends on COM mode. COM3: ~0.4ms
    ctx.push_obligation(ProofObligation::assume("cm", "cycle_ms_x10 == 20")); // 2.0ms
    ctx.push_obligation(ProofObligation::assume("mc", "min_cycle_ms_x10 == 4")); // 0.4ms
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timing_ok == if cycle_ms_x10 >= min_cycle_ms_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timing_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IO-Link: 2.0ms cycle ≥ 0.4ms min → timing OK");
}

#[test]
fn vendor_id() {
    let mut ctx = VerificationContext::new();
    for v in &["vendor_id", "expected_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("id_match", i32_ty());
    // 16-bit vendor ID from IODD
    ctx.push_obligation(ProofObligation::assume("vi", "vendor_id == 310"));
    ctx.push_obligation(ProofObligation::assume("ei", "expected_id == 310"));
    ctx.push_obligation(ProofObligation::assume(
        "im_def",
        "id_match == if vendor_id == expected_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "id_match == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IO-Link: vendor 310 = expected → ID match");
}

#[test]
fn port_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("is_iolink", i32_ty());
    // Port modes: 0=deactivated, 1=DI(SIO), 2=DO(SIO), 3=IO-Link
    ctx.push_obligation(ProofObligation::assume("m", "mode == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ii_def",
        "is_iolink == if mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_iolink == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IO-Link: mode=3 → IO-Link communication");
}

#[test]
fn cable_length() {
    let mut ctx = VerificationContext::new();
    for v in &["cable_m", "max_cable_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("length_ok", i32_ty());
    // IO-Link: max 20m cable length
    ctx.push_obligation(ProofObligation::assume("cm", "cable_m == 15"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cable_m == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "length_ok == if cable_m <= max_cable_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "length_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IO-Link: 15m cable ≤ 20m max → length OK");
}

#[test]
fn isdu_access() {
    let mut ctx = VerificationContext::new();
    for v in &["isdu_index", "max_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("index_valid", i32_ty());
    // ISDU (Indexed Service Data Unit): parameter access 0-65535
    ctx.push_obligation(ProofObligation::assume("ii", "isdu_index == 16"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_index == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "index_valid == if isdu_index <= max_index { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "index_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IO-Link: ISDU index 16 ≤ 65535 → valid");
}

#[test]
fn device_status() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("status", u32_ty());
    ctx.declare_var_typed("is_operational", i32_ty());
    // Status: 0=no device, 1=preoperate, 2=operate, 3=error
    ctx.push_obligation(ProofObligation::assume("s", "status == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "is_operational == if status == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_operational == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IO-Link: status=2 → operational");
}

#[test]
fn event_qualifier() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("event_type", u32_ty());
    ctx.declare_var_typed("is_error_event", i32_ty());
    // Events: 0=reserved, 1=notification, 2=warning, 3=error
    ctx.push_obligation(ProofObligation::assume("et", "event_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ie_def",
        "is_error_event == if event_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_error_event == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IO-Link: event_type=3 → error event");
}

#[test]
fn supply_current() {
    let mut ctx = VerificationContext::new();
    for v in &["device_ma", "port_max_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("current_ok", i32_ty());
    // IO-Link port supplies up to 200mA (Class A) or 1A (Class B)
    ctx.push_obligation(ProofObligation::assume("dm", "device_ma == 150"));
    ctx.push_obligation(ProofObligation::assume("pm", "port_max_ma == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "current_ok == if device_ma <= port_max_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "IO-Link: 150mA device ≤ 200mA port max → current OK",
    );
}
