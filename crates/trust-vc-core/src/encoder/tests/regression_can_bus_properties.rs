// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn standard_frame_id_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("msg_id", u32_ty());
    ctx.declare_var_typed("max_standard_id", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // Standard CAN: 11-bit ID → 0 to 2047
    ctx.push_obligation(ProofObligation::assume("mid", "msg_id == 1500"));
    ctx.push_obligation(ProofObligation::assume("msi", "max_standard_id == 2047")); // 2^11 - 1
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if msg_id <= max_standard_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN: ID 1500 <= 2047 (standard)");
}

#[test]
fn extended_frame_id_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("msg_id", u32_ty());
    ctx.declare_var_typed("max_extended_id", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // Extended CAN: 29-bit ID → max 536870911
    ctx.push_obligation(ProofObligation::assume("mid", "msg_id == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "mei",
        "max_extended_id == 536870911",
    )); // 2^29 - 1
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if msg_id <= max_extended_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN: ID 100000 <= 536870911 (extended)");
}

#[test]
fn data_length_code() {
    let mut ctx = VerificationContext::new();
    for v in &["dlc", "max_dlc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // CAN 2.0: max 8 bytes payload
    ctx.push_obligation(ProofObligation::assume("d", "dlc == 8"));
    ctx.push_obligation(ProofObligation::assume("md", "max_dlc == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if dlc <= max_dlc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN DLC: 8 <= 8");
}

#[test]
fn can_fd_payload_size() {
    let mut ctx = VerificationContext::new();
    for v in &["dlc", "max_fd_payload"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // CAN FD: up to 64 bytes payload
    ctx.push_obligation(ProofObligation::assume("d", "dlc == 48"));
    ctx.push_obligation(ProofObligation::assume("mfp", "max_fd_payload == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if dlc <= max_fd_payload { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: 48 <= 64 bytes");
}

#[test]
fn priority_by_id() {
    // Lower ID = higher priority in CAN arbitration
    let mut ctx = VerificationContext::new();
    for v in &["msg_a_id", "msg_b_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("a_wins", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "msg_a_id == 100"));
    ctx.push_obligation(ProofObligation::assume("b", "msg_b_id == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "aw_def",
        "a_wins == if msg_a_id < msg_b_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "a_wins == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN priority: ID 100 < 500 → A wins");
}

#[test]
fn bit_stuffing_worst_case() {
    // After 5 consecutive same bits, a stuff bit is inserted
    // Worst case: every 5 bits → 1 stuff bit → overhead = data_bits / 5
    let mut ctx = VerificationContext::new();
    for v in &["data_bits", "max_stuff_bits", "total_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("db", "data_bits == 100"));
    ctx.push_obligation(ProofObligation::assume("msb", "max_stuff_bits == 20")); // 100/5
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bits == data_bits + max_stuff_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_120", "total_bits == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "overhead",
        "total_bits > data_bits",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bit stuffing: 100+20=120 worst case");
}

#[test]
fn bus_utilization() {
    let mut ctx = VerificationContext::new();
    for v in &["msg_bits", "bit_time_ns", "msg_time_ns", "period_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("under_capacity", i32_ty());
    // 500kbps → bit time = 2000ns. 120 bits → 240000ns. Period = 1000000ns (1ms)
    ctx.push_obligation(ProofObligation::assume("mb", "msg_bits == 120"));
    ctx.push_obligation(ProofObligation::assume("bt", "bit_time_ns == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "mt_def",
        "msg_time_ns == msg_bits * bit_time_ns",
    ));
    ctx.push_obligation(ProofObligation::assume("p", "period_ns == 1000000"));
    ctx.push_obligation(ProofObligation::assume(
        "uc_def",
        "under_capacity == if msg_time_ns < period_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_240000",
        "msg_time_ns == 240000",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "under_capacity == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "CAN bus: 240000ns < 1000000ns period");
}

#[test]
fn error_frame_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["tx_error_count", "rx_error_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bus_off", i32_ty());
    // Bus-off state when TX error count >= 256
    ctx.push_obligation(ProofObligation::assume("tec", "tx_error_count == 260"));
    ctx.push_obligation(ProofObligation::assume("rec", "rx_error_count == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bus_off == if tx_error_count >= 256 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bus_off == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN: TX errors 260 >= 256 → bus-off");
}

#[test]
fn error_counter_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["old_error_count", "new_error_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Transmit error increments by 8 on error
    ctx.push_obligation(ProofObligation::assume("oec", "old_error_count == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "nec_def",
        "new_error_count == old_error_count + 8",
    ));
    ctx.push_obligation(ProofObligation::assert("is_128", "new_error_count == 128"));
    ctx.push_obligation(ProofObligation::assert(
        "increased",
        "new_error_count > old_error_count",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN error: 120+8=128");
}

#[test]
fn successful_tx_decrements_error() {
    let mut ctx = VerificationContext::new();
    for v in &["old_error_count", "new_error_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Successful transmit decrements by 1
    ctx.push_obligation(ProofObligation::assume("oec", "old_error_count == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "nec_def",
        "new_error_count == old_error_count - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_127", "new_error_count == 127"));
    ctx.push_obligation(ProofObligation::assert(
        "decreased",
        "new_error_count < old_error_count",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN success: 128-1=127 errors");
}
