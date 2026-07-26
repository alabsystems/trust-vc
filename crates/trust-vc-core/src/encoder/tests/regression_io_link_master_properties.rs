// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn port_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ports", "ports_min", "ports_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // IO-Link master port count: value 8, valid range 1 to 16 (typical 4 or 8)
    ctx.push_obligation(ProofObligation::assume("pc_val", "ports == 8"));
    ctx.push_obligation(ProofObligation::assume("pc_min", "ports_min == 1"));
    ctx.push_obligation(ProofObligation::assume("pc_max", "ports_max == 16"));
    ctx.push_obligation(ProofObligation::assert(
        "pc_in_range",
        "ports >= ports_min && ports <= ports_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "port count 8 in range [1,16]");
}

#[test]
fn baud_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud", u32_ty());
    ctx.declare_var_typed("valid_baud", i32_ty());
    // 4800=COM1, 38400=COM2, 230400=COM3 (IEC 61131-9)
    ctx.push_obligation(ProofObligation::assume("br_val", "baud == 230400"));
    ctx.push_obligation(ProofObligation::assume(
        "br_valid_def",
        "valid_baud == if baud == 4800 || baud == 38400 || baud == 230400 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("br_check", "valid_baud == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "baud rate 230400 (COM3) is valid");
}

#[test]
fn process_data_in() {
    let mut ctx = VerificationContext::new();
    for v in &["pdi_bytes", "pdi_min", "pdi_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Process data input in bytes: value 16, valid range 1 to 32
    ctx.push_obligation(ProofObligation::assume("pi_val", "pdi_bytes == 16"));
    ctx.push_obligation(ProofObligation::assume("pi_min", "pdi_min == 1"));
    ctx.push_obligation(ProofObligation::assume("pi_max", "pdi_max == 32"));
    ctx.push_obligation(ProofObligation::assert(
        "pi_in_range",
        "pdi_bytes >= pdi_min && pdi_bytes <= pdi_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "process data in 16 bytes in range [1,32]");
}

#[test]
fn process_data_out() {
    let mut ctx = VerificationContext::new();
    for v in &["pdo_bytes", "pdo_min", "pdo_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Process data output in bytes: value 8, valid range 1 to 32
    ctx.push_obligation(ProofObligation::assume("po_val", "pdo_bytes == 8"));
    ctx.push_obligation(ProofObligation::assume("po_min", "pdo_min == 1"));
    ctx.push_obligation(ProofObligation::assume("po_max", "pdo_max == 32"));
    ctx.push_obligation(ProofObligation::assert(
        "po_in_range",
        "pdo_bytes >= pdo_min && pdo_bytes <= pdo_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "process data out 8 bytes in range [1,32]");
}

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_ms", "cycle_min", "cycle_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Minimum cycle time in ms: value 10, valid range 1 to 200
    ctx.push_obligation(ProofObligation::assume("ct_val", "cycle_ms == 10"));
    ctx.push_obligation(ProofObligation::assume("ct_min", "cycle_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ct_max", "cycle_max == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "ct_in_range",
        "cycle_ms >= cycle_min && cycle_ms <= cycle_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cycle time 10 ms in range [1,200]");
}

#[test]
fn port_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // 1=IO-Link, 2=SIO digital input, 3=SIO digital output, 4=deactivated
    ctx.push_obligation(ProofObligation::assume("pm_val", "mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "pm_valid_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 || mode == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pm_check", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "port mode 1 (IO-Link) is valid");
}

#[test]
fn validation_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vtype", u32_ty());
    ctx.declare_var_typed("valid_vtype", i32_ty());
    // 1=no validation, 2=type compatible, 3=type single
    ctx.push_obligation(ProofObligation::assume("vt_val", "vtype == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_valid_def",
        "valid_vtype == if vtype == 1 || vtype == 2 || vtype == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("vt_check", "valid_vtype == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "validation type 3 (type single) is valid");
}

#[test]
fn fieldbus_interface() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fbus", u32_ty());
    ctx.declare_var_typed("valid_fbus", i32_ty());
    // 1=PROFINET, 2=EtherNet/IP, 3=EtherCAT, 4=Modbus TCP, 5=CC-Link IE
    ctx.push_obligation(ProofObligation::assume("fi_val", "fbus == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "fi_valid_def",
        "valid_fbus == if fbus == 1 || fbus == 2 || fbus == 3 || fbus == 4 || fbus == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fi_check", "valid_fbus == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fieldbus interface 1 (PROFINET) is valid");
}

#[test]
fn isdu_length() {
    let mut ctx = VerificationContext::new();
    for v in &["isdu_bytes", "isdu_min", "isdu_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // ISDU max length in bytes: value 232, valid range 1 to 232
    ctx.push_obligation(ProofObligation::assume("il_val", "isdu_bytes == 232"));
    ctx.push_obligation(ProofObligation::assume("il_min", "isdu_min == 1"));
    ctx.push_obligation(ProofObligation::assume("il_max", "isdu_max == 232"));
    ctx.push_obligation(ProofObligation::assert(
        "il_in_range",
        "isdu_bytes >= isdu_min && isdu_bytes <= isdu_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ISDU length 232 bytes in range [1,232]");
}

#[test]
fn supply_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("supply", u32_ty());
    ctx.declare_var_typed("valid_supply", i32_ty());
    // 1=Class A standard, 2=Class B high power, 3=Class A+B
    ctx.push_obligation(ProofObligation::assume("sc_val", "supply == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "sc_valid_def",
        "valid_supply == if supply == 1 || supply == 2 || supply == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sc_check", "valid_supply == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "supply class 2 (Class B high power) is valid");
}
