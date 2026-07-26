// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn rpi_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rpi_ms", "min_rpi_ms", "max_rpi_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rpi_ok", i32_ty());
    // Requested Packet Interval: cyclic I/O update rate
    ctx.push_obligation(ProofObligation::assume("rm", "rpi_ms == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_rpi_ms == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rpi_ms == 3200"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rpi_ok == if rpi_ms >= min_rpi_ms && rpi_ms <= max_rpi_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rpi_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherNet/IP: RPI 10ms in [1, 3200] → rate OK");
}

#[test]
fn connection_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn_type", u32_ty());
    ctx.declare_var_typed("is_class1", i32_ty());
    // Connection types: 0=explicit (Class 3), 1=implicit/cyclic (Class 1), 2=multicast
    ctx.push_obligation(ProofObligation::assume("ct", "conn_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ic_def",
        "is_class1 == if conn_type == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_class1 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherNet/IP: conn_type=1 → Class 1 implicit");
}

#[test]
fn io_data_size() {
    let mut ctx = VerificationContext::new();
    for v in &["io_bytes", "max_io_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("size_ok", i32_ty());
    // I/O connection data size
    ctx.push_obligation(ProofObligation::assume("ib", "io_bytes == 128"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_io_bytes == 505"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "size_ok == if io_bytes <= max_io_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "size_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherNet/IP: 128B I/O ≤ 505B max → size OK");
}

#[test]
fn tcp_port_number() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("port", u32_ty());
    ctx.declare_var_typed("is_enip", i32_ty());
    // EtherNet/IP uses TCP port 44818 (0xAF12)
    ctx.push_obligation(ProofObligation::assume("p", "port == 44818"));
    ctx.push_obligation(ProofObligation::assume(
        "ie_def",
        "is_enip == if port == 44818 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_enip == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherNet/IP: port=44818 → standard EtherNet/IP");
}

#[test]
fn session_handle() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("session", u32_ty());
    ctx.declare_var_typed("session_valid", i32_ty());
    // Session handle: non-zero indicates active session
    ctx.push_obligation(ProofObligation::assume("s", "session == 12345"));
    ctx.push_obligation(ProofObligation::assume(
        "sv_def",
        "session_valid == if session >= 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "session_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherNet/IP: session 12345 ≥ 1 → valid handle");
}

#[test]
fn encapsulation_command() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("command", u32_ty());
    ctx.declare_var_typed("is_send_rr", i32_ty());
    // Commands: 0x0004=ListServices, 0x0063=ListIdentity, 0x0065=RegisterSession, 0x006F=SendRRData
    ctx.push_obligation(ProofObligation::assume("c", "command == 111")); // 0x006F
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_send_rr == if command == 111 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_send_rr == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherNet/IP: command=0x6F → SendRRData");
}

#[test]
fn cip_service_code() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("service", u32_ty());
    ctx.declare_var_typed("is_get_attr", i32_ty());
    // CIP services: 0x01=Get Attribute All, 0x0E=Get Attribute Single, 0x10=Set Attribute Single
    ctx.push_obligation(ProofObligation::assume("s", "service == 14")); // 0x0E
    ctx.push_obligation(ProofObligation::assume(
        "ig_def",
        "is_get_attr == if service == 14 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_get_attr == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherNet/IP: service=0x0E → Get Attribute Single");
}

#[test]
fn connection_count() {
    let mut ctx = VerificationContext::new();
    for v in &["connections", "max_connections"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("conn_ok", i32_ty());
    // Max CIP connections (device-dependent)
    ctx.push_obligation(ProofObligation::assume("c", "connections == 16"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_connections == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "conn_ok == if connections <= max_connections { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "conn_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherNet/IP: 16 connections ≤ 32 max → OK");
}

#[test]
fn producer_consumer_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["producers", "consumers"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("total", u32_ty());
    // Total I/O connections = producers + consumers
    ctx.push_obligation(ProofObligation::assume("p", "producers == 4"));
    ctx.push_obligation(ProofObligation::assume("c", "consumers == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "t",
        "total == producers + consumers",
    ));
    ctx.push_obligation(ProofObligation::assert("is_12", "total == 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherNet/IP: 4 producers + 8 consumers = 12 total");
}

#[test]
fn device_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dev_type", u32_ty());
    ctx.declare_var_typed("is_adapter", i32_ty());
    // Device types: 0=generic, 2=AC drive, 12=adapter, 43=safety device
    ctx.push_obligation(ProofObligation::assume("dt", "dev_type == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "is_adapter == if dev_type == 12 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_adapter == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherNet/IP: dev_type=12 → communications adapter");
}
