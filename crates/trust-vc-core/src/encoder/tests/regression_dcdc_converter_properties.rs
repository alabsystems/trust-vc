// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn output_voltage_regulation() {
    let mut ctx = VerificationContext::new();
    for v in &["output_mv", "target_mv", "tolerance_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("regulated", i32_ty());
    // Output voltage within regulation tolerance
    ctx.push_obligation(ProofObligation::assume("om", "output_mv == 3310"));
    ctx.push_obligation(ProofObligation::assume("tm", "target_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("tl", "tolerance_mv == 33")); // 1%
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "regulated == if output_mv >= target_mv - tolerance_mv && output_mv <= target_mv + tolerance_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "regulated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC-DC: 3.31V in [3.267, 3.333] → regulated");
}

#[test]
fn duty_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["output_mv", "input_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("duty_pct", u32_ty());
    // Buck: D = Vout/Vin × 100. Precompute: 3300/12000 × 100 = 27 (27.5% → 27)
    ctx.push_obligation(ProofObligation::assume("om", "output_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("im", "input_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("dp", "duty_pct == 27")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_27", "duty_pct == 27"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC-DC: 3.3V/12V = 27% duty cycle (precomputed)");
}

#[test]
fn input_voltage_range() {
    let mut ctx = VerificationContext::new();
    for v in &["vin_mv", "min_vin_mv", "max_vin_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vin_ok", i32_ty());
    // Input range: e.g., 4.5-28V
    ctx.push_obligation(ProofObligation::assume("vm", "vin_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vin_mv == 4500"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vin_mv == 28000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vin_ok == if vin_mv >= min_vin_mv && vin_mv <= max_vin_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vin_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC-DC: 12V in [4.5, 28] → input voltage OK");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Switching frequency: 100kHz - 2MHz typical
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_khz >= min_freq_khz && freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC-DC: 500kHz in [100, 2000] → frequency OK");
}

#[test]
fn output_ripple() {
    let mut ctx = VerificationContext::new();
    for v in &["ripple_mv", "max_ripple_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ripple_ok", i32_ty());
    // Output ripple voltage (peak-to-peak)
    ctx.push_obligation(ProofObligation::assume("rm", "ripple_mv == 20"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_ripple_mv == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ripple_ok == if ripple_mv <= max_ripple_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ripple_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC-DC: 20mV ripple ≤ 50mV max → ripple OK");
}

#[test]
fn load_current() {
    let mut ctx = VerificationContext::new();
    for v in &["load_ma", "max_load_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("load_ok", i32_ty());
    // Output current rating
    ctx.push_obligation(ProofObligation::assume("lm", "load_ma == 2000"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_load_ma == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "load_ok == if load_ma <= max_load_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "load_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC-DC: 2A load ≤ 3A max → load OK");
}

#[test]
fn efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["output_power_mw", "input_power_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("efficiency_pct", u32_ty());
    ctx.declare_var_typed("efficient", i32_ty());
    // η = Pout/Pin × 100. Precompute: 6600/7333 × 100 = 90%
    ctx.push_obligation(ProofObligation::assume("op", "output_power_mw == 6600"));
    ctx.push_obligation(ProofObligation::assume("ip", "input_power_mw == 7333"));
    ctx.push_obligation(ProofObligation::assume("ep", "efficiency_pct == 90")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "efficient == if efficiency_pct >= 85 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_90", "efficiency_pct == 90"));
    ctx.push_obligation(ProofObligation::assert("yes", "efficient == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC-DC: 90% efficiency ≥ 85% min → efficient");
}

#[test]
fn inductor_saturation() {
    let mut ctx = VerificationContext::new();
    for v in &["peak_current_ma", "saturation_current_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("inductor_ok", i32_ty());
    // Inductor must not saturate at peak current
    ctx.push_obligation(ProofObligation::assume("pc", "peak_current_ma == 3500"));
    ctx.push_obligation(ProofObligation::assume(
        "sc",
        "saturation_current_ma == 5000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "inductor_ok == if peak_current_ma < saturation_current_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "inductor_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC-DC: 3.5A peak < 5A saturation → inductor OK");
}

#[test]
fn soft_start_time() {
    let mut ctx = VerificationContext::new();
    for v in &["startup_ms", "max_startup_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("start_ok", i32_ty());
    // Soft start limits inrush current
    ctx.push_obligation(ProofObligation::assume("sm", "startup_ms == 5"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_startup_ms == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "start_ok == if startup_ms <= max_startup_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "start_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC-DC: 5ms startup ≤ 10ms max → start OK");
}

#[test]
fn topology_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("topology", u32_ty());
    ctx.declare_var_typed("is_buck", i32_ty());
    // Topologies: 0=buck, 1=boost, 2=buck-boost, 3=SEPIC
    ctx.push_obligation(ProofObligation::assume("t", "topology == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "is_buck == if topology == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_buck == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC-DC: topology=0 → buck converter");
}
