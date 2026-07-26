// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn turns_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["ratio_x10", "min_ratio_x10", "max_ratio_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ratio_ok", i32_ty());
    // Transformer turns ratio N (×10 for 0.1 precision)
    ctx.push_obligation(ProofObligation::assume("rx", "ratio_x10 == 50")); // 5.0
    ctx.push_obligation(ProofObligation::assume("mn", "min_ratio_x10 == 10")); // 1.0
    ctx.push_obligation(ProofObligation::assume("mx", "max_ratio_x10 == 200")); // 20.0
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ratio_ok == if ratio_x10 >= min_ratio_x10 && ratio_x10 <= max_ratio_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ratio_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flyback: 5.0 turns ratio in [1.0, 20.0] → OK");
}

#[test]
fn output_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vout_mv", "target_mv", "tolerance_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vout_ok", i32_ty());
    // Output voltage regulation
    ctx.push_obligation(ProofObligation::assume("vm", "vout_mv == 5020"));
    ctx.push_obligation(ProofObligation::assume("tm", "target_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("tl", "tolerance_mv == 100")); // 2%
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vout_ok == if vout_mv >= target_mv - tolerance_mv && vout_mv <= target_mv + tolerance_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vout_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flyback: 5.02V in 5.0V ± 2% → output OK");
}

#[test]
fn input_voltage_range() {
    let mut ctx = VerificationContext::new();
    for v in &["vin_mv", "min_vin_mv", "max_vin_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vin_ok", i32_ty());
    // Universal AC input: 85-265Vac rectified → 120-375VDC
    ctx.push_obligation(ProofObligation::assume("vm", "vin_mv == 170000")); // 170V
    ctx.push_obligation(ProofObligation::assume("mn", "min_vin_mv == 120000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vin_mv == 375000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vin_ok == if vin_mv >= min_vin_mv && vin_mv <= max_vin_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vin_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flyback: 170V input in [120, 375] → OK");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Switching frequency
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 65"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_khz >= min_freq_khz && freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flyback: 65kHz in [50, 200] → freq OK");
}

#[test]
fn duty_cycle_max() {
    let mut ctx = VerificationContext::new();
    for v in &["duty_pct", "max_duty_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("duty_ok", i32_ty());
    // Maximum duty cycle (typically 45-50% for flyback)
    ctx.push_obligation(ProofObligation::assume("dp", "duty_pct == 40"));
    ctx.push_obligation(ProofObligation::assume("md", "max_duty_pct == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "duty_ok == if duty_pct <= max_duty_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "duty_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flyback: 40% duty ≤ 50% max → OK");
}

#[test]
fn leakage_inductance() {
    let mut ctx = VerificationContext::new();
    for v in &["leakage_uh_x10", "max_leakage_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("leak_ok", i32_ty());
    // Leakage inductance as % of magnetizing (×10 for 0.1μH)
    ctx.push_obligation(ProofObligation::assume("lx", "leakage_uh_x10 == 20")); // 2.0μH
    ctx.push_obligation(ProofObligation::assume("ml", "max_leakage_x10 == 50")); // 5.0μH
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "leak_ok == if leakage_uh_x10 <= max_leakage_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "leak_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flyback: 2.0μH leakage ≤ 5.0μH max → OK");
}

#[test]
fn snubber_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vsnub_mv", "max_vsnub_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("snub_ok", i32_ty());
    // RCD snubber clamp voltage
    ctx.push_obligation(ProofObligation::assume("vm", "vsnub_mv == 200000")); // 200V
    ctx.push_obligation(ProofObligation::assume("mv", "max_vsnub_mv == 300000")); // 300V
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "snub_ok == if vsnub_mv <= max_vsnub_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "snub_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flyback: 200V snubber ≤ 300V max → OK");
}

#[test]
fn output_power() {
    let mut ctx = VerificationContext::new();
    for v in &["power_mw", "max_power_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_ok", i32_ty());
    // Output power capacity
    ctx.push_obligation(ProofObligation::assume("pm", "power_mw == 15000")); // 15W
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_mw == 65000")); // 65W
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "power_ok == if power_mw <= max_power_mw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flyback: 15W output ≤ 65W max → OK");
}

#[test]
fn cross_regulation() {
    let mut ctx = VerificationContext::new();
    for v in &["cross_reg_pct", "max_cross_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cross_ok", i32_ty());
    // Cross regulation: auxiliary output tracking (lower = better)
    ctx.push_obligation(ProofObligation::assume("cp", "cross_reg_pct == 5"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cross_pct == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cross_ok == if cross_reg_pct <= max_cross_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cross_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flyback: 5% cross regulation ≤ 10% max → OK");
}

#[test]
fn standby_power() {
    let mut ctx = VerificationContext::new();
    for v in &["standby_mw", "max_standby_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stby_ok", i32_ty());
    // No-load/standby power consumption
    ctx.push_obligation(ProofObligation::assume("sm", "standby_mw == 75")); // 75mW
    ctx.push_obligation(ProofObligation::assume("ms", "max_standby_mw == 300")); // 300mW
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stby_ok == if standby_mw <= max_standby_mw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stby_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Flyback: 75mW standby ≤ 300mW max → OK");
}
