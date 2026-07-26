// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn voltage_doubler() {
    let mut ctx = VerificationContext::new();
    for v in &["vin_mv", "vout_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Ideal voltage doubler: Vout = 2 × Vin. Precompute: 2 × 3300 = 6600
    ctx.push_obligation(ProofObligation::assume("vi", "vin_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("vo", "vout_mv == 6600")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_6600", "vout_mv == 6600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charge pump: 3.3V × 2 = 6.6V (precomputed)");
}

#[test]
fn output_regulation() {
    let mut ctx = VerificationContext::new();
    for v in &["vout_mv", "target_mv", "tolerance_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("regulated", i32_ty());
    // Output voltage within regulation tolerance
    ctx.push_obligation(ProofObligation::assume("vo", "vout_mv == 4950"));
    ctx.push_obligation(ProofObligation::assume("tm", "target_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("tl", "tolerance_mv == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "regulated == if vout_mv >= target_mv - tolerance_mv && vout_mv <= target_mv + tolerance_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "regulated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charge pump: 4.95V in [4.9, 5.1] → regulated");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Charge pump switching: 100kHz - 2MHz
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_khz >= min_freq_khz && freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charge pump: 1MHz in [100kHz, 2MHz] → freq OK");
}

#[test]
fn flying_capacitor() {
    let mut ctx = VerificationContext::new();
    for v in &["cap_uf_x10", "min_cap_uf_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cap_ok", i32_ty());
    // Flying capacitor size (×10 for 0.1μF resolution)
    ctx.push_obligation(ProofObligation::assume("cu", "cap_uf_x10 == 10")); // 1.0μF
    ctx.push_obligation(ProofObligation::assume("mc", "min_cap_uf_x10 == 1")); // 0.1μF
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cap_ok == if cap_uf_x10 >= min_cap_uf_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charge pump: 1.0μF cap ≥ 0.1μF min → OK");
}

#[test]
fn output_current() {
    let mut ctx = VerificationContext::new();
    for v in &["load_ma", "max_load_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("load_ok", i32_ty());
    // Charge pump output current (typically 10-300mA)
    ctx.push_obligation(ProofObligation::assume("lm", "load_ma == 100"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_load_ma == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "load_ok == if load_ma <= max_load_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "load_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charge pump: 100mA load ≤ 200mA max → OK");
}

#[test]
fn output_ripple() {
    let mut ctx = VerificationContext::new();
    for v in &["ripple_mv", "max_ripple_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ripple_ok", i32_ty());
    // Output ripple voltage
    ctx.push_obligation(ProofObligation::assume("rm", "ripple_mv == 15"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_ripple_mv == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ripple_ok == if ripple_mv <= max_ripple_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ripple_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charge pump: 15mV ripple ≤ 50mV max → OK");
}

#[test]
fn inverting_output() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("topology", u32_ty());
    ctx.declare_var_typed("is_inverting", i32_ty());
    // Topology: 0=doubler, 1=inverter, 2=regulated, 3=fractional
    ctx.push_obligation(ProofObligation::assume("t", "topology == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ii_def",
        "is_inverting == if topology == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_inverting == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charge pump: topology=1 → inverting output");
}

#[test]
fn efficiency_at_load() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_pct", "min_eff_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eff_ok", i32_ty());
    // Efficiency: regulated charge pumps 80-95%
    ctx.push_obligation(ProofObligation::assume("ep", "eff_pct == 88"));
    ctx.push_obligation(ProofObligation::assume("me", "min_eff_pct == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eff_ok == if eff_pct >= min_eff_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charge pump: 88% efficiency ≥ 80% min → OK");
}

#[test]
fn startup_time() {
    let mut ctx = VerificationContext::new();
    for v in &["startup_us", "max_startup_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("start_ok", i32_ty());
    // Time to reach regulation after enable
    ctx.push_obligation(ProofObligation::assume("su", "startup_us == 200"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_startup_us == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "start_ok == if startup_us <= max_startup_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "start_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charge pump: 200μs startup ≤ 500μs max → OK");
}

#[test]
fn quiescent_current() {
    let mut ctx = VerificationContext::new();
    for v in &["iq_ua", "max_iq_ua"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("iq_ok", i32_ty());
    // Quiescent current (no-load)
    ctx.push_obligation(ProofObligation::assume("iu", "iq_ua == 30"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_iq_ua == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "iq_ok == if iq_ua <= max_iq_ua { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "iq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Charge pump: 30μA Iq ≤ 100μA max → OK");
}
