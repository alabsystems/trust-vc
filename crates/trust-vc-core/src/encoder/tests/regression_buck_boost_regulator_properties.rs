// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn output_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vout_mv", "target_mv", "tolerance_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("regulated", i32_ty());
    // Buck-boost: output stable regardless of input being higher or lower
    ctx.push_obligation(ProofObligation::assume("vo", "vout_mv == 3310"));
    ctx.push_obligation(ProofObligation::assume("tm", "target_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("tl", "tolerance_mv == 66")); // 2%
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "regulated == if vout_mv >= target_mv - tolerance_mv && vout_mv <= target_mv + tolerance_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "regulated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Buck-boost: 3.31V in [3.234, 3.366] → regulated");
}

#[test]
fn input_voltage_range() {
    let mut ctx = VerificationContext::new();
    for v in &["vin_mv", "min_vin_mv", "max_vin_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vin_ok", i32_ty());
    // Wide input: 2.5-5.5V for single-cell Li-ion → 3.3V output
    ctx.push_obligation(ProofObligation::assume("vm", "vin_mv == 3600")); // mid-battery
    ctx.push_obligation(ProofObligation::assume("mn", "min_vin_mv == 2500"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vin_mv == 5500"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vin_ok == if vin_mv >= min_vin_mv && vin_mv <= max_vin_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vin_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Buck-boost: 3.6V in [2.5, 5.5] → input OK");
}

#[test]
fn mode_transition() {
    let mut ctx = VerificationContext::new();
    for v in &["vin_mv", "vout_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_buck", i32_ty());
    // Buck mode when Vin > Vout, boost when Vin < Vout
    ctx.push_obligation(ProofObligation::assume("vi", "vin_mv == 4200"));
    ctx.push_obligation(ProofObligation::assume("vo", "vout_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "is_buck == if vin_mv > vout_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_buck == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Buck-boost: 4.2V > 3.3V → buck mode");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Switching frequency
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 2000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 500"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 4000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_khz >= min_freq_khz && freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Buck-boost: 2MHz in [500kHz, 4MHz] → freq OK");
}

#[test]
fn quiescent_current() {
    let mut ctx = VerificationContext::new();
    for v in &["iq_ua", "max_iq_ua"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("iq_ok", i32_ty());
    // Low Iq critical for battery applications
    ctx.push_obligation(ProofObligation::assume("iu", "iq_ua == 20"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_iq_ua == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "iq_ok == if iq_ua <= max_iq_ua { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "iq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Buck-boost: 20μA Iq ≤ 50μA max → OK");
}

#[test]
fn load_current() {
    let mut ctx = VerificationContext::new();
    for v in &["load_ma", "max_load_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("load_ok", i32_ty());
    // Output current capacity
    ctx.push_obligation(ProofObligation::assume("lm", "load_ma == 500"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_load_ma == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "load_ok == if load_ma <= max_load_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "load_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Buck-boost: 500mA ≤ 1000mA max → load OK");
}

#[test]
fn efficiency_at_light_load() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_pct", "min_eff_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eff_ok", i32_ty());
    // Light-load efficiency with PFM mode
    ctx.push_obligation(ProofObligation::assume("ep", "eff_pct == 92"));
    ctx.push_obligation(ProofObligation::assume("me", "min_eff_pct == 85"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eff_ok == if eff_pct >= min_eff_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Buck-boost: 92% efficiency ≥ 85% min → OK");
}

#[test]
fn inductor_value() {
    let mut ctx = VerificationContext::new();
    for v in &["inductor_uh_x10", "min_uh_x10", "max_uh_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ind_ok", i32_ty());
    // Inductor selection (×10 for 0.1μH resolution)
    ctx.push_obligation(ProofObligation::assume("iu", "inductor_uh_x10 == 22")); // 2.2μH
    ctx.push_obligation(ProofObligation::assume("mn", "min_uh_x10 == 10")); // 1.0μH
    ctx.push_obligation(ProofObligation::assume("mx", "max_uh_x10 == 100")); // 10.0μH
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "ind_ok == if inductor_uh_x10 >= min_uh_x10 && inductor_uh_x10 <= max_uh_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ind_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Buck-boost: 2.2μH in [1.0, 10.0] → inductor OK");
}

#[test]
fn output_ripple() {
    let mut ctx = VerificationContext::new();
    for v in &["ripple_mv", "max_ripple_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ripple_ok", i32_ty());
    // Output voltage ripple
    ctx.push_obligation(ProofObligation::assume("rm", "ripple_mv == 10"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_ripple_mv == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ripple_ok == if ripple_mv <= max_ripple_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ripple_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Buck-boost: 10mV ripple ≤ 30mV max → OK");
}

#[test]
fn shutdown_current() {
    let mut ctx = VerificationContext::new();
    for v in &["ishdn_na", "max_ishdn_na"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("shdn_ok", i32_ty());
    // Shutdown current (nA range for battery longevity)
    ctx.push_obligation(ProofObligation::assume("in", "ishdn_na == 100"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_ishdn_na == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "shdn_ok == if ishdn_na <= max_ishdn_na { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "shdn_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Buck-boost: 100nA shutdown ≤ 500nA max → OK");
}
