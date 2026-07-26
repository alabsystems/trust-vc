// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn baud_rate_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud_rate", u32_ty());
    ctx.declare_var_typed("is_valid", i32_ty());
    // LIN bus standard baud rates: 2400, 9600, 19200
    ctx.push_obligation(ProofObligation::assume("br", "baud_rate == 19200"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "is_valid == if baud_rate == 2400 || baud_rate == 9600 || baud_rate == 19200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIN: 19200 baud → valid baud rate");
}

#[test]
fn frame_id_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frame_id", u32_ty());
    ctx.declare_var_typed("id_valid", i32_ty());
    // LIN frame ID: 0-59 (signal carrying), 60-61 (diagnostic), 62-63 (reserved)
    ctx.push_obligation(ProofObligation::assume("fi", "frame_id == 45"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "id_valid == if frame_id <= 63 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "id_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIN: frame ID 45 ≤ 63 → valid ID");
}

#[test]
fn data_length() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bytes", "max_data_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("length_ok", i32_ty());
    // LIN frame: 1-8 data bytes
    ctx.push_obligation(ProofObligation::assume("db", "data_bytes == 4"));
    ctx.push_obligation(ProofObligation::assume("md", "max_data_bytes == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "length_ok == if data_bytes >= 1 && data_bytes <= max_data_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "length_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIN: 4 bytes in [1, 8] → valid data length");
}

#[test]
fn sync_break_length() {
    let mut ctx = VerificationContext::new();
    for v in &["break_bits", "min_break_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("break_ok", i32_ty());
    // Sync break: minimum 13 bit times for master
    ctx.push_obligation(ProofObligation::assume("bb", "break_bits == 15"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_break_bits == 13"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "break_ok == if break_bits >= min_break_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "break_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIN: 15 break bits ≥ 13 min → break OK");
}

#[test]
fn slave_response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["response_bits", "max_response_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timing_ok", i32_ty());
    // Response space: max depends on data length
    ctx.push_obligation(ProofObligation::assume("rb", "response_bits == 50"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_response_bits == 110"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timing_ok == if response_bits <= max_response_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timing_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIN: 50 response bits ≤ 110 max → timing OK");
}

#[test]
fn checksum_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lin_version", u32_ty());
    ctx.declare_var_typed("use_enhanced", i32_ty());
    // LIN 1.x: classic checksum (data only), LIN 2.x: enhanced (data + PID)
    // Version: 1=LIN1.x, 2=LIN2.x
    ctx.push_obligation(ProofObligation::assume("lv", "lin_version == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ue_def",
        "use_enhanced == if lin_version >= 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "use_enhanced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIN: version 2 → use enhanced checksum");
}

#[test]
fn node_count() {
    let mut ctx = VerificationContext::new();
    for v in &["slave_count", "max_slaves"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("count_ok", i32_ty());
    // LIN bus: 1 master + up to 15 slaves (16 nodes total)
    ctx.push_obligation(ProofObligation::assume("sc", "slave_count == 8"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_slaves == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "count_ok == if slave_count <= max_slaves { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "count_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIN: 8 slaves ≤ 15 max → count OK");
}

#[test]
fn wakeup_signal() {
    let mut ctx = VerificationContext::new();
    for v in &["wakeup_pulse_us", "min_wakeup_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wakeup_valid", i32_ty());
    // Wakeup pulse: 250μs to 5ms dominant
    ctx.push_obligation(ProofObligation::assume("wp", "wakeup_pulse_us == 500"));
    ctx.push_obligation(ProofObligation::assume("mw", "min_wakeup_us == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "wv_def",
        "wakeup_valid == if wakeup_pulse_us >= min_wakeup_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "wakeup_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIN: 500μs wakeup ≥ 250μs min → valid wakeup");
}

#[test]
fn diagnostic_frame() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frame_id", u32_ty());
    ctx.declare_var_typed("is_diagnostic", i32_ty());
    // Diagnostic frames: ID 60 (master request) and 61 (slave response)
    ctx.push_obligation(ProofObligation::assume("fi", "frame_id == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "id_def",
        "is_diagnostic == if frame_id == 60 || frame_id == 61 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_diagnostic == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIN: frame ID 60 → diagnostic frame");
}

#[test]
fn bus_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["bus_voltage_mv", "min_voltage_mv", "max_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voltage_ok", i32_ty());
    // LIN bus voltage: 7-18V (automotive 12V nominal)
    ctx.push_obligation(ProofObligation::assume("bv", "bus_voltage_mv == 13500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_voltage_mv == 7000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_voltage_mv == 18000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "voltage_ok == if bus_voltage_mv >= min_voltage_mv && bus_voltage_mv <= max_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "voltage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LIN: 13.5V in [7, 18] → bus voltage OK");
}
