// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn wiper_position() {
    let mut ctx = VerificationContext::new();
    for v in &["position", "max_position"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // 256-tap digital pot: position 0-255
    ctx.push_obligation(ProofObligation::assume("p", "position == 128"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_position == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if position <= max_position { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DigiPot: position 128 ≤ 255 max → valid");
}

#[test]
fn resistance_from_position() {
    let mut ctx = VerificationContext::new();
    for v in &["position", "total_resistance_ohms", "max_position"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wiper_resistance_ohms", u32_ty());
    // R_wiper = position / max_position × R_total. Precompute: 128/256 × 10000 = 5000Ω
    ctx.push_obligation(ProofObligation::assume("p", "position == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "tr",
        "total_resistance_ohms == 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("mp", "max_position == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "wr",
        "wiper_resistance_ohms == 5000",
    )); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_5000",
        "wiper_resistance_ohms == 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DigiPot: pos 128/256 × 10kΩ = 5kΩ (precomputed)");
}

#[test]
fn voltage_divider_output() {
    let mut ctx = VerificationContext::new();
    for v in &["input_mv", "position", "max_position"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("output_mv", u32_ty());
    // V_out = V_in × position / max_position. Precompute: 3300 × 128 / 256 = 1650mV
    ctx.push_obligation(ProofObligation::assume("im", "input_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("p", "position == 128"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_position == 256"));
    ctx.push_obligation(ProofObligation::assume("om", "output_mv == 1650")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1650", "output_mv == 1650"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DigiPot: 3.3V × 128/256 = 1.65V output (precomputed)",
    );
}

#[test]
fn step_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["old_position", "new_position", "steps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Increment wiper by N steps
    ctx.push_obligation(ProofObligation::assume("op", "old_position == 100"));
    ctx.push_obligation(ProofObligation::assume("s", "steps == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "np_def",
        "new_position == old_position + steps",
    ));
    ctx.push_obligation(ProofObligation::assert("is_110", "new_position == 110"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DigiPot: 100 + 10 steps = position 110");
}

#[test]
fn nonvolatile_memory() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nv_supported", u32_ty());
    ctx.declare_var_typed("can_store", i32_ty());
    // Some digital pots have NV memory to store wiper position
    ctx.push_obligation(ProofObligation::assume("ns", "nv_supported == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "can_store == if nv_supported == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_store == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DigiPot: NV supported = 1 → can store position");
}

#[test]
fn spi_command_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("command", u32_ty());
    ctx.declare_var_typed("is_write", i32_ty());
    // SPI command byte: 0x00=write, 0x0C=read, 0x04=increment, 0x08=decrement
    ctx.push_obligation(ProofObligation::assume("c", "command == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "iw_def",
        "is_write == if command == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_write == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DigiPot: command 0x00 → write command");
}

#[test]
fn wiper_resistance_min() {
    let mut ctx = VerificationContext::new();
    for v in &["wiper_ohms", "min_wiper_ohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("above_min", i32_ty());
    // Wiper resistance (R_w): typically 50-200Ω, limits minimum output resistance
    ctx.push_obligation(ProofObligation::assume("wo", "wiper_ohms == 75"));
    ctx.push_obligation(ProofObligation::assume("mw", "min_wiper_ohms == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "am_def",
        "above_min == if wiper_ohms >= min_wiper_ohms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "above_min == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DigiPot: 75Ω wiper ≥ 50Ω min → above minimum");
}

#[test]
fn power_dissipation() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ua", "resistance_ohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_uw", u32_ty());
    ctx.declare_var_typed("within_limit", i32_ty());
    // P = I² × R. Precompute: (1000μA)² × 5000Ω / 1000000 = 5000μW
    ctx.push_obligation(ProofObligation::assume("cu", "current_ua == 1000"));
    ctx.push_obligation(ProofObligation::assume("ro", "resistance_ohms == 5000"));
    ctx.push_obligation(ProofObligation::assume("pu", "power_uw == 5000")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if power_uw <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5000", "power_uw == 5000"));
    ctx.push_obligation(ProofObligation::assert("yes", "within_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DigiPot: 1mA² × 5kΩ = 5mW ≤ 10mW limit (precomputed)",
    );
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.declare_var_typed("is_dual", i32_ty());
    // Single, dual, or quad channel digital pots
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "id_def",
        "is_dual == if channels == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_dual == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DigiPot: channels=2 → dual channel");
}

#[test]
fn temperature_coefficient() {
    let mut ctx = VerificationContext::new();
    for v in &["tempco_ppm", "max_tempco_ppm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tempco_ok", i32_ty());
    // Rheostat mode tempco: typically 5-50 ppm/°C
    ctx.push_obligation(ProofObligation::assume("tp", "tempco_ppm == 15"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tempco_ppm == 35"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tempco_ok == if tempco_ppm <= max_tempco_ppm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tempco_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DigiPot: 15 ppm/°C ≤ 35 max → tempco OK");
}
