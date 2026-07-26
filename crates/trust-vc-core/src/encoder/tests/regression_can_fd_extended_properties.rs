// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn data_phase_bitrate() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bps", "max_data_bps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // CAN FD data phase: up to 8 Mbps (vs 1 Mbps classic CAN)
    ctx.push_obligation(ProofObligation::assume("db", "data_bps == 5000000"));
    ctx.push_obligation(ProofObligation::assume("md", "max_data_bps == 8000000"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if data_bps <= max_data_bps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: 5 Mbps data ≤ 8 Mbps max → rate OK");
}

#[test]
fn payload_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dlc", u32_ty());
    ctx.declare_var_typed("valid_dlc", i32_ty());
    // CAN FD DLC: 0-8 bytes (classic), 12, 16, 20, 24, 32, 48, 64 bytes
    ctx.push_obligation(ProofObligation::assume("d", "dlc == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_dlc == if dlc <= 64 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_dlc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: DLC 64 ≤ 64 max → valid payload");
}

#[test]
fn arbitration_phase_bitrate() {
    let mut ctx = VerificationContext::new();
    for v in &["arb_bps", "min_arb_bps", "max_arb_bps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("arb_ok", i32_ty());
    // Arbitration phase: 125kbps-1Mbps (same as classic CAN)
    ctx.push_obligation(ProofObligation::assume("ab", "arb_bps == 500000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_arb_bps == 125000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_arb_bps == 1000000"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "arb_ok == if arb_bps >= min_arb_bps && arb_bps <= max_arb_bps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "arb_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: 500kbps arb in [125k, 1M] → OK");
}

#[test]
fn brs_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("brs", u32_ty());
    ctx.declare_var_typed("rate_switch", i32_ty());
    // BRS (Bit Rate Switch): 0=no switch (classic rate), 1=switch to data phase rate
    ctx.push_obligation(ProofObligation::assume("b", "brs == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "rs_def",
        "rate_switch == if brs == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_switch == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: BRS=1 → bit rate switch active");
}

#[test]
fn esi_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("esi", u32_ty());
    ctx.declare_var_typed("is_error_passive", i32_ty());
    // ESI (Error State Indicator): 0=error active, 1=error passive
    ctx.push_obligation(ProofObligation::assume("e", "esi == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ip_def",
        "is_error_passive == if esi == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "is_error_passive == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: ESI=0 → error active (not passive)");
}

#[test]
fn crc_polynomial() {
    let mut ctx = VerificationContext::new();
    for v in &["payload_bytes", "crc_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("crc_correct", i32_ty());
    // CAN FD CRC: 17-bit for ≤16 bytes, 21-bit for >16 bytes
    ctx.push_obligation(ProofObligation::assume("pb", "payload_bytes == 32"));
    ctx.push_obligation(ProofObligation::assume("cb", "crc_bits == 21"));
    ctx.push_obligation(ProofObligation::assume(
        "cc_def",
        "crc_correct == if payload_bytes > 16 && crc_bits == 21 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "crc_correct == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: 32 bytes > 16 → 21-bit CRC correct");
}

#[test]
fn stuff_bit_count() {
    let mut ctx = VerificationContext::new();
    for v in &["stuff_bits", "max_stuff_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stuff_ok", i32_ty());
    // Fixed stuff bits in CAN FD data phase (deterministic, not dynamic)
    ctx.push_obligation(ProofObligation::assume("sb", "stuff_bits == 4"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_stuff_bits == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stuff_ok == if stuff_bits <= max_stuff_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stuff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: 4 stuff bits ≤ 8 max → OK");
}

#[test]
fn transceiver_delay() {
    let mut ctx = VerificationContext::new();
    for v in &["tdc_ns", "max_tdc_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tdc_ok", i32_ty());
    // Transceiver Delay Compensation: critical at high data rates
    ctx.push_obligation(ProofObligation::assume("tn", "tdc_ns == 150"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tdc_ns == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tdc_ok == if tdc_ns <= max_tdc_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tdc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: 150ns TDC ≤ 250ns max → delay OK");
}

#[test]
fn message_id_range() {
    let mut ctx = VerificationContext::new();
    for v in &["msg_id", "max_std_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_standard", i32_ty());
    // Standard (11-bit): 0-2047, Extended (29-bit): 0-536870911
    ctx.push_obligation(ProofObligation::assume("mi", "msg_id == 1500"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_std_id == 2047"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_standard == if msg_id <= max_std_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_standard == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: ID 1500 ≤ 2047 → standard frame");
}

#[test]
fn bus_load() {
    let mut ctx = VerificationContext::new();
    for v in &["load_pct", "max_load_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("load_ok", i32_ty());
    // Bus load: keep below ~70-80% for reliable operation
    ctx.push_obligation(ProofObligation::assume("lp", "load_pct == 45"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_load_pct == 70"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "load_ok == if load_pct <= max_load_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "load_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CAN FD: 45% bus load ≤ 70% max → OK");
}
