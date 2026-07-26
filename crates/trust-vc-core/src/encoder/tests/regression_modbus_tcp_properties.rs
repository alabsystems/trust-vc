// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn transaction_id() {
    let mut ctx = VerificationContext::new();
    for v in &["request_id", "response_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("id_match", i32_ty());
    // Modbus TCP: transaction ID in response must match request
    ctx.push_obligation(ProofObligation::assume("ri", "request_id == 42"));
    ctx.push_obligation(ProofObligation::assume("si", "response_id == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "im_def",
        "id_match == if request_id == response_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "id_match == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Modbus TCP: request ID 42 == response ID 42 → match",
    );
}

#[test]
fn protocol_id() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("protocol_id", u32_ty());
    ctx.declare_var_typed("is_modbus", i32_ty());
    // Modbus TCP protocol ID must be 0
    ctx.push_obligation(ProofObligation::assume("pi", "protocol_id == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "im_def",
        "is_modbus == if protocol_id == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_modbus == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus TCP: protocol_id=0 → valid Modbus");
}

#[test]
fn unit_id() {
    let mut ctx = VerificationContext::new();
    for v in &["unit_id", "max_unit_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // Unit identifier: 0-247 (248-255 reserved)
    ctx.push_obligation(ProofObligation::assume("ui", "unit_id == 10"));
    ctx.push_obligation(ProofObligation::assume("mu", "max_unit_id == 247"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if unit_id <= max_unit_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus TCP: unit ID 10 ≤ 247 → valid");
}

#[test]
fn function_code() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fc", u32_ty());
    ctx.declare_var_typed("is_read_holding", i32_ty());
    // Common function codes: 1=read coils, 2=read DI, 3=read holding, 4=read input, 5=write coil, 6=write register
    ctx.push_obligation(ProofObligation::assume("f", "fc == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_read_holding == if fc == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_read_holding == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus TCP: FC=3 → read holding registers");
}

#[test]
fn register_address() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "max_address"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("addr_ok", i32_ty());
    // Register address: 0-65535
    ctx.push_obligation(ProofObligation::assume("a", "address == 40001"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_address == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "addr_ok == if address <= max_address { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus TCP: address 40001 ≤ 65535 → valid");
}

#[test]
fn quantity_of_registers() {
    let mut ctx = VerificationContext::new();
    for v in &["quantity", "min_quantity", "max_quantity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("qty_ok", i32_ty());
    // Read holding registers: 1-125 registers per request
    ctx.push_obligation(ProofObligation::assume("q", "quantity == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_quantity == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_quantity == 125"));
    ctx.push_obligation(ProofObligation::assume(
        "qo_def",
        "qty_ok == if quantity >= min_quantity && quantity <= max_quantity { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "qty_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Modbus TCP: 10 registers in [1, 125] → quantity OK",
    );
}

#[test]
fn mbap_length() {
    let mut ctx = VerificationContext::new();
    for v in &["pdu_bytes", "mbap_length"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // MBAP length = unit ID (1 byte) + PDU bytes
    ctx.push_obligation(ProofObligation::assume("pb", "pdu_bytes == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ml",
        "mbap_length == pdu_bytes + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "mbap_length == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Modbus TCP: PDU 5 bytes + 1 unit ID = MBAP length 6",
    );
}

#[test]
fn exception_response() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("response_fc", u32_ty());
    ctx.declare_var_typed("is_exception", i32_ty());
    // Exception: response FC = request FC + 128 (bit 7 set)
    ctx.push_obligation(ProofObligation::assume("rf", "response_fc == 131")); // 3 + 128
    ctx.push_obligation(ProofObligation::assume(
        "ie_def",
        "is_exception == if response_fc >= 128 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_exception == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus TCP: FC 131 ≥ 128 → exception response");
}

#[test]
fn tcp_port() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("port", u32_ty());
    ctx.declare_var_typed("is_standard", i32_ty());
    // Standard Modbus TCP port: 502
    ctx.push_obligation(ProofObligation::assume("p", "port == 502"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_standard == if port == 502 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_standard == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus TCP: port=502 → standard port");
}

#[test]
fn connection_count() {
    let mut ctx = VerificationContext::new();
    for v in &["connections", "max_connections"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("conn_ok", i32_ty());
    // Max simultaneous TCP connections (server-dependent)
    ctx.push_obligation(ProofObligation::assume("c", "connections == 5"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_connections == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "conn_ok == if connections <= max_connections { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "conn_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus TCP: 5 connections ≤ 16 max → OK");
}
