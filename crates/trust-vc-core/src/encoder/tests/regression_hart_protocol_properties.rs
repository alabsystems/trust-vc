// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn current_loop() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma_x10", "min_ma_x10", "max_ma_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("loop_ok", i32_ty());
    // 4-20mA current loop: ×10 scale → 40-200
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma_x10 == 120")); // 12.0mA
    ctx.push_obligation(ProofObligation::assume("mn", "min_ma_x10 == 40")); // 4.0mA
    ctx.push_obligation(ProofObligation::assume("mx", "max_ma_x10 == 200")); // 20.0mA
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "loop_ok == if current_ma_x10 >= min_ma_x10 && current_ma_x10 <= max_ma_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "loop_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HART: 12.0mA in [4.0, 20.0] → loop current OK");
}

#[test]
fn pv_scaling() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma_x10", "pv_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // PV = (I - 4) / 16 × span + LRV. Precompute: (12-4)/16 × 1000 = 500 (50.0%)
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma_x10 == 120"));
    ctx.push_obligation(ProofObligation::assume("pv", "pv_x10 == 500")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_500", "pv_x10 == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HART: 12mA → 50.0% PV (precomputed)");
}

#[test]
fn device_address() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "max_address"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // HART: short address 0-15 (0=primary), long address up to 38-bit
    ctx.push_obligation(ProofObligation::assume("a", "address == 5"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_address == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if address <= max_address { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HART: address 5 ≤ 15 max → valid short address");
}

#[test]
fn baud_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud", u32_ty());
    ctx.declare_var_typed("is_standard", i32_ty());
    // HART: 1200 baud FSK on 4-20mA
    ctx.push_obligation(ProofObligation::assume("b", "baud == 1200"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_standard == if baud == 1200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_standard == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HART: baud=1200 → standard HART rate");
}

#[test]
fn command_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cmd_number", u32_ty());
    ctx.declare_var_typed("is_universal", i32_ty());
    // Universal commands: 0-30, Common Practice: 32-126, Device Specific: 128-253
    ctx.push_obligation(ProofObligation::assume("cn", "cmd_number == 1")); // Read PV
    ctx.push_obligation(ProofObligation::assume(
        "iu_def",
        "is_universal == if cmd_number <= 30 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_universal == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HART: cmd 1 ≤ 30 → universal command");
}

#[test]
fn preamble_count() {
    let mut ctx = VerificationContext::new();
    for v in &["preambles", "min_preambles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("preamble_ok", i32_ty());
    // HART frame: minimum 5 preamble bytes (0xFF)
    ctx.push_obligation(ProofObligation::assume("p", "preambles == 5"));
    ctx.push_obligation(ProofObligation::assume("mp", "min_preambles == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "preamble_ok == if preambles >= min_preambles { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "preamble_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HART: 5 preambles ≥ 5 min → preamble OK");
}

#[test]
fn loop_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["total_ohms", "min_ohms", "max_ohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resistance_ok", i32_ty());
    // Loop resistance: 250-1100Ω for HART communication
    ctx.push_obligation(ProofObligation::assume("to", "total_ohms == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ohms == 250"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ohms == 1100"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resistance_ok == if total_ohms >= min_ohms && total_ohms <= max_ohms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resistance_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HART: 500Ω in [250, 1100] → loop resistance OK");
}

#[test]
fn multidrop_mode() {
    let mut ctx = VerificationContext::new();
    for v in &["device_count", "max_devices"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("count_ok", i32_ty());
    // HART multidrop: up to 15 devices (address 1-15)
    ctx.push_obligation(ProofObligation::assume("dc", "device_count == 8"));
    ctx.push_obligation(ProofObligation::assume("md", "max_devices == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "count_ok == if device_count <= max_devices { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "count_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HART: 8 devices ≤ 15 max → multidrop OK");
}

#[test]
fn fsk_frequencies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mark_hz", u32_ty());
    ctx.declare_var_typed("space_hz", u32_ty());
    ctx.declare_var_typed("mark_correct", i32_ty());
    // HART FSK: mark (1) = 1200Hz, space (0) = 2200Hz
    ctx.push_obligation(ProofObligation::assume("mh", "mark_hz == 1200"));
    ctx.push_obligation(ProofObligation::assume("sh", "space_hz == 2200"));
    ctx.push_obligation(ProofObligation::assume(
        "mc_def",
        "mark_correct == if mark_hz == 1200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mark_correct == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HART: mark=1200Hz → correct FSK frequency");
}

#[test]
fn burst_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("burst_enabled", u32_ty());
    ctx.declare_var_typed("is_burst", i32_ty());
    // Burst mode: continuous data transmission without polling
    ctx.push_obligation(ProofObligation::assume("be", "burst_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "is_burst == if burst_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_burst == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HART: burst_enabled=1 → burst mode active");
}
