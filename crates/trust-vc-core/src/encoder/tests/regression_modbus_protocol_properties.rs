// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn slave_address_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("slave_addr", u32_ty());
    ctx.declare_var_typed("is_unicast", i32_ty());
    // Modbus: 1-247 = unicast, 0 = broadcast, 248-255 = reserved
    ctx.push_obligation(ProofObligation::assume("sa", "slave_addr == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "iu_def",
        "is_unicast == if slave_addr >= 1 && slave_addr <= 247 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_unicast == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus: addr 10 in [1, 247] → unicast");
}

#[test]
fn function_code_read() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("func_code", u32_ty());
    ctx.declare_var_typed("is_read", i32_ty());
    // FC 1-4 are read functions
    ctx.push_obligation(ProofObligation::assume("fc", "func_code == 3")); // Read Holding Registers
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_read == if func_code >= 1 && func_code <= 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_read == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus: FC 3 (Read Holding Registers) → is read");
}

#[test]
fn register_count_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["register_count", "max_registers"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("count_ok", i32_ty());
    // Max 125 registers per read request (FC 3/4)
    ctx.push_obligation(ProofObligation::assume("rc", "register_count == 100"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_registers == 125"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "count_ok == if register_count >= 1 && register_count <= max_registers { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "count_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus: 100 registers in [1, 125] → count OK");
}

#[test]
fn coil_address_range() {
    let mut ctx = VerificationContext::new();
    for v in &["coil_addr", "max_coil_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("addr_valid", i32_ty());
    // Coil addresses: 0-65535 (0x0000-0xFFFF)
    ctx.push_obligation(ProofObligation::assume("ca", "coil_addr == 1000"));
    ctx.push_obligation(ProofObligation::assume("mca", "max_coil_addr == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "av_def",
        "addr_valid == if coil_addr <= max_coil_addr { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus: coil addr 1000 ≤ 65535 → valid");
}

#[test]
fn exception_response() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("response_code", u32_ty());
    ctx.declare_var_typed("is_exception", i32_ty());
    // Exception response: function code + 0x80 (128). FC 3 exception = 131.
    ctx.push_obligation(ProofObligation::assume("rc", "response_code == 131"));
    ctx.push_obligation(ProofObligation::assume(
        "ie_def",
        "is_exception == if response_code >= 128 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_exception == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus: response 131 ≥ 128 → exception response");
}

#[test]
fn rtu_frame_size() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bytes", "overhead_bytes", "total_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("size_ok", i32_ty());
    // RTU frame: 1 addr + 1 FC + data + 2 CRC = data + 4 overhead. Max 256 bytes.
    ctx.push_obligation(ProofObligation::assume("db", "data_bytes == 250"));
    ctx.push_obligation(ProofObligation::assume("ob", "overhead_bytes == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bytes == data_bytes + overhead_bytes",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "size_ok == if total_bytes <= 256 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_254", "total_bytes == 254"));
    ctx.push_obligation(ProofObligation::assert("yes", "size_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus RTU: 250 + 4 = 254 ≤ 256 max → size OK");
}

#[test]
fn tcp_transaction_id() {
    let mut ctx = VerificationContext::new();
    for v in &["request_id", "response_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("id_match", i32_ty());
    // Modbus TCP: transaction ID in request must match response
    ctx.push_obligation(ProofObligation::assume("ri", "request_id == 42"));
    ctx.push_obligation(ProofObligation::assume("rsi", "response_id == 42"));
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
fn baud_rate_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud_rate", u32_ty());
    ctx.declare_var_typed("is_standard", i32_ty());
    // Standard Modbus baud: 9600 or 19200
    ctx.push_obligation(ProofObligation::assume("br", "baud_rate == 9600"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_standard == if baud_rate == 9600 || baud_rate == 19200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_standard == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus: baud 9600 → standard rate");
}

#[test]
fn inter_frame_gap() {
    let mut ctx = VerificationContext::new();
    for v in &["gap_char_times", "min_gap_chars"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("gap_ok", i32_ty());
    // Modbus RTU: minimum 3.5 character times between frames (use 4 for integer)
    ctx.push_obligation(ProofObligation::assume("gc", "gap_char_times == 5"));
    ctx.push_obligation(ProofObligation::assume("mg", "min_gap_chars == 4")); // 3.5 rounded up
    ctx.push_obligation(ProofObligation::assume(
        "go_def",
        "gap_ok == if gap_char_times >= min_gap_chars { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "gap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus RTU: 5 char times ≥ 4 min → gap OK");
}

#[test]
fn write_single_register() {
    let mut ctx = VerificationContext::new();
    for v in &["register_value", "min_value", "max_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("value_ok", i32_ty());
    // Modbus register is 16-bit: 0-65535
    ctx.push_obligation(ProofObligation::assume("rv", "register_value == 1024"));
    ctx.push_obligation(ProofObligation::assume("mnv", "min_value == 0"));
    ctx.push_obligation(ProofObligation::assume("mxv", "max_value == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "value_ok == if register_value >= min_value && register_value <= max_value { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "value_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus: register value 1024 in [0, 65535] → valid");
}
