// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn analog_input_range() {
    let mut ctx = VerificationContext::new();
    for v in &["input_mv", "min_input_mv", "max_input_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("input_ok", i32_ty());
    // Analog input: 0-10V (in mV) or 4-20mA
    ctx.push_obligation(ProofObligation::assume("im", "input_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_input_mv == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_input_mv == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "input_ok == if input_mv >= min_input_mv && input_mv <= max_input_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "input_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC IO: 5000mV in [0, 10000] → analog input OK");
}

#[test]
fn digital_output() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("state", u32_ty());
    ctx.declare_var_typed("valid_state", i32_ty());
    // Digital output: 0 or 1
    ctx.push_obligation(ProofObligation::assume("s", "state == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_state == if state == 0 || state == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_state == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC IO: state=1 → valid digital output");
}

#[test]
fn scan_cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["scan_us", "max_scan_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("scan_ok", i32_ty());
    // PLC scan cycle: determines IO update rate
    ctx.push_obligation(ProofObligation::assume("su", "scan_us == 500"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_scan_us == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "scan_ok == if scan_us <= max_scan_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "scan_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC IO: 500μs scan ≤ 10ms max → OK");
}

#[test]
fn io_point_count() {
    let mut ctx = VerificationContext::new();
    for v in &["points", "max_points"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("points_ok", i32_ty());
    // Total IO points per module
    ctx.push_obligation(ProofObligation::assume("p", "points == 16"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_points == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "points_ok == if points <= max_points { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "points_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC IO: 16 points ≤ 64 max → OK");
}

#[test]
fn module_slot() {
    let mut ctx = VerificationContext::new();
    for v in &["slot", "max_slots"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("slot_ok", i32_ty());
    // Module slot in backplane (0-indexed)
    ctx.push_obligation(ProofObligation::assume("s", "slot == 3"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_slots == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "slot_ok == if slot < max_slots { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "slot_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC IO: slot 3 < 16 max → OK");
}

#[test]
fn communication_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_mbps", "min_rate_mbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Backplane communication rate
    ctx.push_obligation(ProofObligation::assume("rm", "rate_mbps == 100"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_rate_mbps == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if rate_mbps >= min_rate_mbps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC IO: 100Mbps ≥ 10Mbps min → rate OK");
}

#[test]
fn diagnostics_register() {
    let mut ctx = VerificationContext::new();
    for v in &["diag_bits", "min_diag_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("diag_ok", i32_ty());
    // Diagnostics register width
    ctx.push_obligation(ProofObligation::assume("db", "diag_bits == 16"));
    ctx.push_obligation(ProofObligation::assume("md", "min_diag_bits == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "diag_ok == if diag_bits >= min_diag_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "diag_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC IO: 16-bit diagnostics ≥ 8-bit min → OK");
}

#[test]
fn watchdog_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["timeout_ms", "min_timeout_ms", "max_timeout_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wd_ok", i32_ty());
    // IO module watchdog: safe state on communication loss
    ctx.push_obligation(ProofObligation::assume("tm", "timeout_ms == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_timeout_ms == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_timeout_ms == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "wd_ok == if timeout_ms >= min_timeout_ms && timeout_ms <= max_timeout_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "wd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC IO: 200ms watchdog in [10, 5000] → OK");
}

#[test]
fn redundancy_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Redundancy: 0=none, 1=hot-standby, 2=dual-channel
    ctx.push_obligation(ProofObligation::assume("m", "mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 0 || mode == 1 || mode == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC IO: mode=1 → valid hot-standby redundancy");
}

#[test]
fn memory_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &["used_bytes", "total_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mem_ok", i32_ty());
    // IO module process image memory
    ctx.push_obligation(ProofObligation::assume("ub", "used_bytes == 256"));
    ctx.push_obligation(ProofObligation::assume("tb", "total_bytes == 1024"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mem_ok == if used_bytes <= total_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mem_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PLC IO: 256 bytes ≤ 1024 total → memory OK");
}
