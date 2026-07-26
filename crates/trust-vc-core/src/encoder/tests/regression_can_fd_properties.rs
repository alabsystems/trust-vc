// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn can_fd_payload_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dlc", u32_ty());
    ctx.declare_var_typed("payload_bytes", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // CAN FD DLC mapping: DLC 9→12, 10→16, 11→20, 12→24, 13→32, 14→48, 15→64
    // DLC 13 → 32 bytes
    ctx.push_obligation(ProofObligation::assume("d", "dlc == 13"));
    ctx.push_obligation(ProofObligation::assume("pb", "payload_bytes == 32")); // precomputed mapping
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if payload_bytes <= 64 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_32", "payload_bytes == 32"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: DLC 13 → 32 bytes (valid ≤ 64)");
}

#[test]
fn arbitration_id_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["id_a", "id_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("a_wins", i32_ty());
    // CAN: lower ID = higher priority
    ctx.push_obligation(ProofObligation::assume("ia", "id_a == 100"));
    ctx.push_obligation(ProofObligation::assume("ib", "id_b == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "aw_def",
        "a_wins == if id_a < id_b { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "a_wins == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN: ID 100 < 200 → message A wins arbitration");
}

#[test]
fn extended_id_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("can_id", u32_ty());
    ctx.declare_var_typed("is_extended", i32_ty());
    ctx.declare_var_typed("valid_extended", i32_ty());
    // Standard: 11-bit (0-2047), Extended: 29-bit (0-536870911)
    ctx.push_obligation(ProofObligation::assume("ci", "can_id == 5000")); // > 2047
    ctx.push_obligation(ProofObligation::assume(
        "ie_def",
        "is_extended == if can_id > 2047 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ve_def",
        "valid_extended == if can_id <= 536870911 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ext", "is_extended == 1"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_extended == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN: ID 5000 > 2047 → extended, ≤ 29-bit max");
}

#[test]
fn bit_rate_switch() {
    let mut ctx = VerificationContext::new();
    for v in &["arbitration_rate_kbps", "data_rate_kbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("brs_valid", i32_ty());
    // CAN FD BRS: data rate >= arbitration rate
    ctx.push_obligation(ProofObligation::assume(
        "ark",
        "arbitration_rate_kbps == 500",
    ));
    ctx.push_obligation(ProofObligation::assume("drk", "data_rate_kbps == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "bv_def",
        "brs_valid == if data_rate_kbps >= arbitration_rate_kbps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "brs_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD BRS: 2Mbps data ≥ 500kbps arb → valid");
}

#[test]
fn bus_off_error_count() {
    let mut ctx = VerificationContext::new();
    for v in &["tx_error_count", "bus_off_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bus_off", i32_ty());
    // CAN: bus-off when TX error counter ≥ 256
    ctx.push_obligation(ProofObligation::assume("tec", "tx_error_count == 260"));
    ctx.push_obligation(ProofObligation::assume("bot", "bus_off_threshold == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bus_off == if tx_error_count >= bus_off_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bus_off == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN: TX errors 260 ≥ 256 → bus-off");
}

#[test]
fn message_acceptance_filter() {
    let mut ctx = VerificationContext::new();
    for v in &["msg_id", "filter_id", "filter_mask"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("accepted", i32_ty());
    // Acceptance: (msg_id & mask) == (filter_id & mask)
    // Precompute: both mask to same value
    // msg_id=0x123 (291), filter=0x120 (288), mask=0xFF0 (4080)
    // 291 & 4080 = 288, 288 & 4080 = 288 → match
    ctx.push_obligation(ProofObligation::assume("mi", "msg_id == 291"));
    ctx.push_obligation(ProofObligation::assume("fi", "filter_id == 288"));
    ctx.push_obligation(ProofObligation::assume("accepted_val", "accepted == 1")); // precomputed
    ctx.push_obligation(ProofObligation::assert("yes", "accepted == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "CAN filter: 0x123 & 0xFF0 == 0x120 & 0xFF0 → accepted",
    );
}

#[test]
fn transmit_mailbox_selection() {
    let mut ctx = VerificationContext::new();
    for v in &["mb0_empty", "mb1_empty", "mb2_empty"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("selected_mb", u32_ty());
    // Select first empty mailbox (0 = empty, 1 = full)
    ctx.push_obligation(ProofObligation::assume("m0", "mb0_empty == 1")); // full
    ctx.push_obligation(ProofObligation::assume("m1", "mb1_empty == 0")); // empty
    ctx.push_obligation(ProofObligation::assume("m2", "mb2_empty == 0")); // empty
    ctx.push_obligation(ProofObligation::assume(
        "sm_def",
        "selected_mb == if mb0_empty == 0 { 0 } else { if mb1_empty == 0 { 1 } else { 2 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "selected_mb == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN TX: MB0 full, MB1 empty → select MB1");
}

#[test]
fn timestamp_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["timer_freq_mhz", "timestamp_bits", "max_time_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // CAN FD timestamp: 16-bit timer at bus clock
    // At 80MHz: max = 65535 / 80 ≈ 819us. Precompute.
    ctx.push_obligation(ProofObligation::assume("tf", "timer_freq_mhz == 80"));
    ctx.push_obligation(ProofObligation::assume("tb", "timestamp_bits == 16"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_time_us == 819")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_819", "max_time_us == 819"));
    ctx.push_obligation(ProofObligation::assert("positive", "max_time_us > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: 16-bit @ 80MHz → 819us max timestamp");
}

#[test]
fn fifo_fill_level() {
    let mut ctx = VerificationContext::new();
    for v in &["rx_fifo_count", "fifo_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fifo_full", i32_ty());
    ctx.declare_var_typed("fifo_near_full", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rfc", "rx_fifo_count == 5"));
    ctx.push_obligation(ProofObligation::assume("fd", "fifo_depth == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "ff_def",
        "fifo_full == if rx_fifo_count >= fifo_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "fnf_def",
        "fifo_near_full == if rx_fifo_count >= fifo_depth - 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("not_full", "fifo_full == 0"));
    ctx.push_obligation(ProofObligation::assert("near_full", "fifo_near_full == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FIFO: 5/6 → not full, but near full");
}

#[test]
fn error_passive_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["rx_error_count", "passive_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("error_passive", i32_ty());
    // CAN: error passive when error counter ≥ 128
    ctx.push_obligation(ProofObligation::assume("rec", "rx_error_count == 130"));
    ctx.push_obligation(ProofObligation::assume("pt", "passive_threshold == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "error_passive == if rx_error_count >= passive_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "error_passive == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN: RX errors 130 ≥ 128 → error passive");
}
