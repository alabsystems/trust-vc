// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn slave_address() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "max_address"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("addr_ok", i32_ty());
    // Modbus ASCII slave address (1-247, 0=broadcast)
    ctx.push_obligation(ProofObligation::assume("a", "address == 10"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_address == 247"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "addr_ok == if address >= 1 && address <= max_address { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus ASCII: address 10 in [1, 247] → OK");
}

#[test]
fn function_code() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("func", u32_ty());
    ctx.declare_var_typed("valid_func", i32_ty());
    // Common function codes: 1=ReadCoils, 2=ReadDiscreteInputs, 3=ReadHoldingRegisters,
    // 4=ReadInputRegisters, 5=WriteSingleCoil, 6=WriteSingleRegister, 15=WriteMultipleCoils, 16=WriteMultipleRegisters
    ctx.push_obligation(ProofObligation::assume("f", "func == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_func == if func == 1 || func == 2 || func == 3 || func == 4 || func == 5 || func == 6 || func == 15 || func == 16 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_func == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus ASCII: ReadHoldingRegisters (3) is valid");
}

#[test]
fn register_count() {
    let mut ctx = VerificationContext::new();
    for v in &["registers", "max_registers"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("reg_ok", i32_ty());
    // Number of registers in a single request (max 125 for read, 123 for write)
    ctx.push_obligation(ProofObligation::assume("r", "registers == 10"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_registers == 125"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "reg_ok == if registers >= 1 && registers <= max_registers { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "reg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus ASCII: 10 registers in [1, 125] → OK");
}

#[test]
fn frame_length() {
    let mut ctx = VerificationContext::new();
    for v in &["frame_chars", "max_frame_chars"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("frame_ok", i32_ty());
    // ASCII frame length in characters (each byte = 2 hex chars + overhead)
    ctx.push_obligation(ProofObligation::assume("fc", "frame_chars == 34"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_frame_chars == 513"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "frame_ok == if frame_chars >= 9 && frame_chars <= max_frame_chars { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "frame_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus ASCII: 34-char frame in [9, 513] → OK");
}

#[test]
fn baud_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud", u32_ty());
    ctx.declare_var_typed("valid_baud", i32_ty());
    // Standard serial baud rates
    ctx.push_obligation(ProofObligation::assume("b", "baud == 9600"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_baud == if baud == 1200 || baud == 2400 || baud == 4800 || baud == 9600 || baud == 19200 || baud == 38400 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_baud == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus ASCII: 9600 is valid baud rate");
}

#[test]
fn parity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("parity", u32_ty());
    ctx.declare_var_typed("valid_parity", i32_ty());
    // Parity settings: 0=none, 1=even, 2=odd
    ctx.push_obligation(ProofObligation::assume("p", "parity == 1")); // even (default)
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_parity == if parity == 0 || parity == 1 || parity == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_parity == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus ASCII: even parity is valid");
}

#[test]
fn inter_char_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["timeout_ms", "max_timeout_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("to_ok", i32_ty());
    // Inter-character timeout in ms (1 second for ASCII mode)
    ctx.push_obligation(ProofObligation::assume("tm", "timeout_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_timeout_ms == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "to_ok == if timeout_ms <= max_timeout_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "to_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus ASCII: 1s inter-char timeout ≤ 5s max → OK");
}

#[test]
fn coil_count() {
    let mut ctx = VerificationContext::new();
    for v in &["coils", "max_coils"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("coil_ok", i32_ty());
    // Number of coils in a single read (max 2000)
    ctx.push_obligation(ProofObligation::assume("c", "coils == 100"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_coils == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "coil_ok == if coils >= 1 && coils <= max_coils { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "coil_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus ASCII: 100 coils in [1, 2000] → OK");
}

#[test]
fn register_address() {
    let mut ctx = VerificationContext::new();
    for v in &["reg_addr", "max_reg_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("addr_ok", i32_ty());
    // Register address (16-bit, 0-65535)
    ctx.push_obligation(ProofObligation::assume("ra", "reg_addr == 40001"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_reg_addr == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "addr_ok == if reg_addr <= max_reg_addr { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Modbus ASCII: register 40001 ≤ 65535 max → OK");
}

#[test]
fn exception_code() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("exc", u32_ty());
    ctx.declare_var_typed("valid_exc", i32_ty());
    // Standard exception codes: 1=illegal function, 2=illegal data address,
    // 3=illegal data value, 4=slave device failure, 6=slave device busy
    ctx.push_obligation(ProofObligation::assume("e", "exc == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ve_def",
        "valid_exc == if exc == 1 || exc == 2 || exc == 3 || exc == 4 || exc == 6 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_exc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Modbus ASCII: illegal data address (2) is valid exception",
    );
}
