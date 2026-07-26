// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn power_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["pf_x100", "min_pf_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pf_ok", i32_ty());
    // PFC output: PF > 0.99 typically (×100 → 99)
    ctx.push_obligation(ProofObligation::assume("pf", "pf_x100 == 99"));
    ctx.push_obligation(ProofObligation::assume("mp", "min_pf_x100 == 95"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pf_ok == if pf_x100 >= min_pf_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PFC: PF 0.99 ≥ 0.95 min → power factor OK");
}

#[test]
fn thd_current() {
    let mut ctx = VerificationContext::new();
    for v in &["thd_pct_x10", "max_thd_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("thd_ok", i32_ty());
    // Total Harmonic Distortion: < 5% typical for Class D (×10 scale)
    ctx.push_obligation(ProofObligation::assume("tp", "thd_pct_x10 == 30")); // 3.0%
    ctx.push_obligation(ProofObligation::assume("mt", "max_thd_x10 == 50")); // 5.0%
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "thd_ok == if thd_pct_x10 <= max_thd_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "thd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PFC: THD 3.0% ≤ 5.0% max → distortion OK");
}

#[test]
fn dc_bus_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vbus_mv", "target_mv", "tolerance_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vbus_ok", i32_ty());
    // Regulated DC bus output (e.g., 400V for universal input)
    ctx.push_obligation(ProofObligation::assume("vm", "vbus_mv == 398000")); // 398V
    ctx.push_obligation(ProofObligation::assume("tm", "target_mv == 400000")); // 400V
    ctx.push_obligation(ProofObligation::assume("tl", "tolerance_mv == 8000")); // ±8V (2%)
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vbus_ok == if vbus_mv >= target_mv - tolerance_mv && vbus_mv <= target_mv + tolerance_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vbus_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PFC: 398V bus in [392, 408] → regulated OK");
}

#[test]
fn input_voltage_range() {
    let mut ctx = VerificationContext::new();
    for v in &["vin_vrms_x10", "min_vin_x10", "max_vin_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vin_ok", i32_ty());
    // Universal input: 90-264 Vrms (×10 scale)
    ctx.push_obligation(ProofObligation::assume("vv", "vin_vrms_x10 == 2300")); // 230V
    ctx.push_obligation(ProofObligation::assume("mn", "min_vin_x10 == 900")); // 90V
    ctx.push_obligation(ProofObligation::assume("mx", "max_vin_x10 == 2640")); // 264V
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vin_ok == if vin_vrms_x10 >= min_vin_x10 && vin_vrms_x10 <= max_vin_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vin_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PFC: 230Vrms in [90, 264] → universal input OK");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // PFC switching frequency: 50-200kHz typical
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_khz >= min_freq_khz && freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PFC: 100kHz in [50, 200] → switching freq OK");
}

#[test]
fn efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["efficiency_x10", "min_eff_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eff_ok", i32_ty());
    // PFC stage efficiency: typically 95-98% (×10 scale)
    ctx.push_obligation(ProofObligation::assume("ex", "efficiency_x10 == 970")); // 97.0%
    ctx.push_obligation(ProofObligation::assume("me", "min_eff_x10 == 950")); // 95.0%
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eff_ok == if efficiency_x10 >= min_eff_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PFC: 97.0% efficiency ≥ 95.0% min → OK");
}

#[test]
fn conduction_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("is_ccm", i32_ty());
    // Conduction modes: 0=DCM (discontinuous), 1=CCM (continuous), 2=CrCM (critical)
    ctx.push_obligation(ProofObligation::assume("m", "mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ic_def",
        "is_ccm == if mode == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_ccm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PFC: mode=1 → continuous conduction mode");
}

#[test]
fn inrush_current() {
    let mut ctx = VerificationContext::new();
    for v in &["inrush_a_x10", "max_inrush_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("inrush_ok", i32_ty());
    // Inrush current limited by soft-start
    ctx.push_obligation(ProofObligation::assume("ia", "inrush_a_x10 == 200")); // 20.0A
    ctx.push_obligation(ProofObligation::assume("mi", "max_inrush_x10 == 500")); // 50.0A
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "inrush_ok == if inrush_a_x10 <= max_inrush_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "inrush_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PFC: 20A inrush ≤ 50A max → OK");
}

#[test]
fn output_power() {
    let mut ctx = VerificationContext::new();
    for v in &["power_w", "max_power_w"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_ok", i32_ty());
    // Output power rating
    ctx.push_obligation(ProofObligation::assume("pw", "power_w == 600"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_w == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "power_ok == if power_w <= max_power_w { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PFC: 600W output ≤ 1000W max → power OK");
}

#[test]
fn hold_up_time() {
    let mut ctx = VerificationContext::new();
    for v in &["holdup_ms", "min_holdup_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("holdup_ok", i32_ty());
    // Hold-up time: how long DC bus stays in regulation after AC loss
    ctx.push_obligation(ProofObligation::assume("hm", "holdup_ms == 20"));
    ctx.push_obligation(ProofObligation::assume("mh", "min_holdup_ms == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "holdup_ok == if holdup_ms >= min_holdup_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "holdup_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PFC: 20ms hold-up ≥ 16ms min → OK");
}
