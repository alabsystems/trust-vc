// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["flow_lpm_x10", "max_flow_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("flow_ok", i32_ty());
    // Rated flow in liters per minute (×10 for 0.1 LPM)
    ctx.push_obligation(ProofObligation::assume("fx", "flow_lpm_x10 == 400")); // 40.0 LPM
    ctx.push_obligation(ProofObligation::assume("mf", "max_flow_x10 == 800")); // 80.0 LPM
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "flow_ok == if flow_lpm_x10 <= max_flow_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "flow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hydraulic: 40.0 LPM flow ≤ 80.0 max → OK");
}

#[test]
fn operating_pressure() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure_bar", "min_pressure", "max_pressure"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("press_ok", i32_ty());
    // Operating pressure range in bar
    ctx.push_obligation(ProofObligation::assume("pb", "pressure_bar == 210"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pressure == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pressure == 350"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "press_ok == if pressure_bar >= min_pressure && pressure_bar <= max_pressure { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "press_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hydraulic: 210 bar in [50, 350] → OK");
}

#[test]
fn spool_position() {
    let mut ctx = VerificationContext::new();
    for v in &["pos_x100", "min_pos_x100", "max_pos_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pos_ok", i32_ty());
    // Spool position ×100 for 0.01mm precision (offset +5000 for ±50mm range)
    ctx.push_obligation(ProofObligation::assume("px", "pos_x100 == 5250")); // +2.50mm
    ctx.push_obligation(ProofObligation::assume("mn", "min_pos_x100 == 0")); // -50.00mm
    ctx.push_obligation(ProofObligation::assume("mx", "max_pos_x100 == 10000")); // +50.00mm
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pos_ok == if pos_x100 >= min_pos_x100 && pos_x100 <= max_pos_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pos_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hydraulic: spool +2.50mm in [-50, +50] → OK");
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["response_ms", "max_response_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resp_ok", i32_ty());
    // Step response time in milliseconds
    ctx.push_obligation(ProofObligation::assume("rm", "response_ms == 8"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_response_ms == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if response_ms <= max_response_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hydraulic: 8ms response ≤ 20ms max → OK");
}

#[test]
fn hysteresis() {
    let mut ctx = VerificationContext::new();
    for v in &["hyst_x10", "max_hyst_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hyst_ok", i32_ty());
    // Hysteresis as % of full stroke (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("hx", "hyst_x10 == 5")); // 0.5%
    ctx.push_obligation(ProofObligation::assume("mh", "max_hyst_x10 == 30")); // 3.0%
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hyst_ok == if hyst_x10 <= max_hyst_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hyst_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hydraulic: 0.5% hysteresis ≤ 3.0% max → OK");
}

#[test]
fn leakage_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["leak_ml_per_min", "max_leak"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("leak_ok", i32_ty());
    // Internal leakage in mL/min
    ctx.push_obligation(ProofObligation::assume("lm", "leak_ml_per_min == 20"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_leak == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "leak_ok == if leak_ml_per_min <= max_leak { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "leak_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hydraulic: 20 mL/min leakage ≤ 100 max → OK");
}

#[test]
fn dither_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["dither_hz", "min_dither_hz", "max_dither_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dith_ok", i32_ty());
    // Dither signal frequency to reduce spool stiction
    ctx.push_obligation(ProofObligation::assume("dh", "dither_hz == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_dither_hz == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_dither_hz == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dith_ok == if dither_hz >= min_dither_hz && dither_hz <= max_dither_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dith_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hydraulic: 200Hz dither in [50, 400] → OK");
}

#[test]
fn null_bias() {
    let mut ctx = VerificationContext::new();
    for v in &["bias_pct_x10", "max_bias_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bias_ok", i32_ty());
    // Null bias (center offset) as % of rated flow (×10)
    ctx.push_obligation(ProofObligation::assume("bx", "bias_pct_x10 == 10")); // 1.0%
    ctx.push_obligation(ProofObligation::assume("mb", "max_bias_x10 == 30")); // 3.0%
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bias_ok == if bias_pct_x10 <= max_bias_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bias_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hydraulic: 1.0% null bias ≤ 3.0% max → OK");
}

#[test]
fn valve_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve_config", u32_ty());
    ctx.declare_var_typed("valid_config", i32_ty());
    // Valve configurations: 2-way, 3-way, 4-way (2, 3, 4)
    ctx.push_obligation(ProofObligation::assume("vc", "valve_config == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_config == if valve_config == 2 || valve_config == 3 || valve_config == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_config == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hydraulic: 4-way valve is valid config");
}

#[test]
fn coil_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "max_current_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("coil_ok", i32_ty());
    // Solenoid coil drive current
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma == 600"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_ma == 1200"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "coil_ok == if current_ma <= max_current_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "coil_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hydraulic: 600mA coil ≤ 1200mA max → OK");
}
