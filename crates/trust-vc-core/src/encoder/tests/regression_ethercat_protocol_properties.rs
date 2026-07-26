// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_us", "max_cycle_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("realtime_ok", i32_ty());
    // EtherCAT cycle time: sub-millisecond typical
    ctx.push_obligation(ProofObligation::assume("cu", "cycle_us == 250"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cycle_us == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "realtime_ok == if cycle_us <= max_cycle_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "realtime_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherCAT: 250μs cycle ≤ 1000μs max → realtime OK");
}

#[test]
fn slave_count() {
    let mut ctx = VerificationContext::new();
    for v in &["num_slaves", "max_slaves"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("count_ok", i32_ty());
    // EtherCAT: up to 65535 slaves on one segment
    ctx.push_obligation(ProofObligation::assume("ns", "num_slaves == 32"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_slaves == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "count_ok == if num_slaves <= max_slaves { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "count_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherCAT: 32 slaves ≤ 65535 max → count OK");
}

#[test]
fn datagram_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cmd_type", u32_ty());
    ctx.declare_var_typed("is_logical", i32_ty());
    // Commands: 0=NOP, 1=APRD, 2=APWR, 4=FPRD, 5=FPWR, 7=BRD, 8=BWR, 10=LRD, 11=LWR, 12=LRW
    // Logical addressing: LRD(10), LWR(11), LRW(12)
    ctx.push_obligation(ProofObligation::assume("ct", "cmd_type == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "il_def",
        "is_logical == if cmd_type == 10 || cmd_type == 11 || cmd_type == 12 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_logical == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherCAT: cmd=12 (LRW) → logical addressing");
}

#[test]
fn working_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["wkc", "expected_wkc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wkc_ok", i32_ty());
    // Working counter: incremented by each slave that processes the datagram
    ctx.push_obligation(ProofObligation::assume("w", "wkc == 32"));
    ctx.push_obligation(ProofObligation::assume("ew", "expected_wkc == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "wkc_ok == if wkc == expected_wkc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "wkc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EtherCAT: WKC 32 = expected 32 → all slaves responded",
    );
}

#[test]
fn slave_state() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("state", u32_ty());
    ctx.declare_var_typed("is_operational", i32_ty());
    // States: 1=Init, 2=Pre-Op, 4=Safe-Op, 8=Operational
    ctx.push_obligation(ProofObligation::assume("s", "state == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "is_operational == if state == 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_operational == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherCAT: state=8 → Operational");
}

#[test]
fn pdo_mapping_size() {
    let mut ctx = VerificationContext::new();
    for v in &["pdo_bits", "max_pdo_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mapping_ok", i32_ty());
    // Process Data Object mapping: total bits must fit in FMMU allocation
    ctx.push_obligation(ProofObligation::assume("pb", "pdo_bits == 64"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pdo_bits == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mapping_ok == if pdo_bits <= max_pdo_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mapping_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherCAT: 64-bit PDO ≤ 128-bit max → mapping OK");
}

#[test]
fn distributed_clock() {
    let mut ctx = VerificationContext::new();
    for v in &["drift_ns", "max_drift_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sync_ok", i32_ty());
    // DC synchronization: sub-microsecond drift between slaves
    ctx.push_obligation(ProofObligation::assume("dn", "drift_ns == 50"));
    ctx.push_obligation(ProofObligation::assume("md", "max_drift_ns == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sync_ok == if drift_ns <= max_drift_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sync_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherCAT: 50ns drift ≤ 100ns max → DC sync OK");
}

#[test]
fn frame_size() {
    let mut ctx = VerificationContext::new();
    for v in &["payload_bytes", "max_payload_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("size_ok", i32_ty());
    // EtherCAT frame: up to 1486 bytes payload (Ethernet MTU - headers)
    ctx.push_obligation(ProofObligation::assume("pb", "payload_bytes == 1000"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_payload_bytes == 1486"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "size_ok == if payload_bytes <= max_payload_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "size_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherCAT: 1000 bytes ≤ 1486 max → frame size OK");
}

#[test]
fn topology_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("port_count", u32_ty());
    ctx.declare_var_typed("is_junction", i32_ty());
    // Port topology: 1=end device, 2=passthrough, 3+=junction
    ctx.push_obligation(ProofObligation::assume("pc", "port_count == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ij_def",
        "is_junction == if port_count >= 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_junction == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EtherCAT: 3 ports → junction device");
}

#[test]
fn sdo_access() {
    let mut ctx = VerificationContext::new();
    for v in &["index", "max_index"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("index_valid", i32_ty());
    // Service Data Object: CoE object dictionary (0x1000-0x9FFF)
    ctx.push_obligation(ProofObligation::assume("i", "index == 4096")); // 0x1000
    ctx.push_obligation(ProofObligation::assume("mi", "max_index == 40959")); // 0x9FFF
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "index_valid == if index >= 4096 && index <= max_index { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "index_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EtherCAT: index 0x1000 in [0x1000, 0x9FFF] → SDO valid",
    );
}
