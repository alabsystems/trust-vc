// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn input_voltage_range() {
    let mut ctx = VerificationContext::new();
    for v in &["vin_v", "min_vin_v", "max_vin_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vin_ok", i32_ty());
    // AC input voltage range
    ctx.push_obligation(ProofObligation::assume("vv", "vin_v == 230"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vin_v == 85")); // universal
    ctx.push_obligation(ProofObligation::assume("mx", "max_vin_v == 264"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vin_ok == if vin_v >= min_vin_v && vin_v <= max_vin_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vin_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SMPS: 230V input in [85, 264] universal → OK");
}

#[test]
fn output_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vout_mv", "target_mv", "tolerance_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vout_ok", i32_ty());
    // Output voltage regulation (tolerance band)
    ctx.push_obligation(ProofObligation::assume("vm", "vout_mv == 12050")); // 12.05V
    ctx.push_obligation(ProofObligation::assume("tm", "target_mv == 12000")); // 12.00V
    ctx.push_obligation(ProofObligation::assume("tv", "tolerance_mv == 120")); // ±120mV (1%)
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vout_ok == if vout_mv >= target_mv - tolerance_mv && vout_mv <= target_mv + tolerance_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vout_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SMPS: 12.05V within ±1% of 12.00V → OK");
}

#[test]
fn efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_x10", "min_eff_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eff_ok", i32_ty());
    // Efficiency % (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("ex", "eff_x10 == 920")); // 92.0%
    ctx.push_obligation(ProofObligation::assume("me", "min_eff_x10 == 870")); // 87.0% min
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eff_ok == if eff_x10 >= min_eff_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SMPS: 92.0% efficiency ≥ 87.0% min → OK");
}

#[test]
fn topology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("topo", u32_ty());
    ctx.declare_var_typed("valid_topo", i32_ty());
    // SMPS topologies: 1=buck, 2=boost, 3=buck-boost, 4=flyback, 5=forward, 6=LLC resonant
    ctx.push_obligation(ProofObligation::assume("t", "topo == 6")); // LLC
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_topo == if topo == 1 || topo == 2 || topo == 3 || topo == 4 || topo == 5 || topo == 6 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_topo == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SMPS: LLC resonant is valid topology");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Switching frequency in kHz
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 30"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_khz >= min_freq_khz && freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SMPS: 100 kHz switching in [30, 1000] → OK");
}

#[test]
fn ripple_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["ripple_mv", "max_ripple_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rip_ok", i32_ty());
    // Output voltage ripple peak-to-peak in mV
    ctx.push_obligation(ProofObligation::assume("rm", "ripple_mv == 50"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_ripple_mv == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rip_ok == if ripple_mv <= max_ripple_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rip_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SMPS: 50mV ripple ≤ 200mV max → OK");
}

#[test]
fn power_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["power_w", "max_power_w"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pow_ok", i32_ty());
    // Output power in watts
    ctx.push_obligation(ProofObligation::assume("pw", "power_w == 150"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_w == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pow_ok == if power_w <= max_power_w { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pow_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SMPS: 150W output ≤ 1000W max → OK");
}

#[test]
fn standby_power() {
    let mut ctx = VerificationContext::new();
    for v in &["standby_mw", "max_standby_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stby_ok", i32_ty());
    // No-load standby power in mW
    ctx.push_obligation(ProofObligation::assume("sm", "standby_mw == 100")); // 0.1W
    ctx.push_obligation(ProofObligation::assume("ms", "max_standby_mw == 500")); // 0.5W (ERP)
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stby_ok == if standby_mw <= max_standby_mw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stby_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SMPS: 0.1W standby ≤ 0.5W ERP max → OK");
}

#[test]
fn hold_up_time() {
    let mut ctx = VerificationContext::new();
    for v in &["holdup_ms", "min_holdup_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hu_ok", i32_ty());
    // Hold-up time after AC loss in ms
    ctx.push_obligation(ProofObligation::assume("hm", "holdup_ms == 20"));
    ctx.push_obligation(ProofObligation::assume("mh", "min_holdup_ms == 10")); // 10ms = half cycle
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hu_ok == if holdup_ms >= min_holdup_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hu_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SMPS: 20ms hold-up ≥ 10ms min → OK");
}

#[test]
fn isolation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["iso_vac", "min_iso_vac"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("iso_ok", i32_ty());
    // Input-output isolation voltage VAC
    ctx.push_obligation(ProofObligation::assume("iv", "iso_vac == 3000"));
    ctx.push_obligation(ProofObligation::assume("mi", "min_iso_vac == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "iso_ok == if iso_vac >= min_iso_vac { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "iso_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SMPS: 3000 VAC isolation ≥ 1500 min → OK");
}
