// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn resonant_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "min_freq_hz", "max_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Piezo resonant frequency must match vibration source
    ctx.push_obligation(ProofObligation::assume("fh", "freq_hz == 120"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_hz == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_hz == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_hz >= min_freq_hz && freq_hz <= max_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo harvester: 120Hz in [50, 500] → freq OK");
}

#[test]
fn voltage_output() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "min_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("volt_ok", i32_ty());
    // Open-circuit voltage must exceed rectifier threshold
    ctx.push_obligation(ProofObligation::assume("vm", "voltage_mv == 3500"));
    ctx.push_obligation(ProofObligation::assume("mv", "min_voltage_mv == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "volt_ok == if voltage_mv >= min_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "volt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo harvester: 3.5V output ≥ 1.0V min → OK");
}

#[test]
fn power_density() {
    let mut ctx = VerificationContext::new();
    for v in &["power_uw_per_cm3", "min_power"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pwr_ok", i32_ty());
    // Power density: μW/cm³
    ctx.push_obligation(ProofObligation::assume("pu", "power_uw_per_cm3 == 200"));
    ctx.push_obligation(ProofObligation::assume("mp", "min_power == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pwr_ok == if power_uw_per_cm3 >= min_power { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pwr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo harvester: 200μW/cm³ ≥ 50 min → density OK");
}

#[test]
fn capacitor_storage() {
    let mut ctx = VerificationContext::new();
    for v in &["cap_uf", "min_cap_uf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cap_ok", i32_ty());
    // Storage capacitor size for energy buffering
    ctx.push_obligation(ProofObligation::assume("cu", "cap_uf == 100"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_cap_uf == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cap_ok == if cap_uf >= min_cap_uf { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo harvester: 100μF ≥ 10μF min → storage OK");
}

#[test]
fn rectifier_efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_pct", "min_eff_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eff_ok", i32_ty());
    // Rectifier (active bridge) efficiency
    ctx.push_obligation(ProofObligation::assume("ep", "eff_pct == 90"));
    ctx.push_obligation(ProofObligation::assume("me", "min_eff_pct == 70"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eff_ok == if eff_pct >= min_eff_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo harvester: 90% rectifier ≥ 70% min → OK");
}

#[test]
fn vibration_amplitude() {
    let mut ctx = VerificationContext::new();
    for v in &["amp_mg", "min_amp_mg", "max_amp_mg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("amp_ok", i32_ty());
    // Input vibration amplitude in milli-g
    ctx.push_obligation(ProofObligation::assume("am", "amp_mg == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_amp_mg == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_amp_mg == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "amp_ok == if amp_mg >= min_amp_mg && amp_mg <= max_amp_mg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "amp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo harvester: 500mg in [100, 2000] → OK");
}

#[test]
fn impedance_matching() {
    let mut ctx = VerificationContext::new();
    for v in &["load_ohm", "optimal_ohm", "tolerance_ohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("match_ok", i32_ty());
    // Load impedance should match source for max power transfer
    ctx.push_obligation(ProofObligation::assume("lo", "load_ohm == 4800"));
    ctx.push_obligation(ProofObligation::assume("oo", "optimal_ohm == 5000"));
    ctx.push_obligation(ProofObligation::assume("to", "tolerance_ohm == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "match_ok == if load_ohm >= optimal_ohm - tolerance_ohm && load_ohm <= optimal_ohm + tolerance_ohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "match_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Piezo harvester: 4.8kΩ load in 5kΩ ± 1kΩ → matched",
    );
}

#[test]
fn load_regulation() {
    let mut ctx = VerificationContext::new();
    for v in &["reg_pct", "max_reg_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("reg_ok", i32_ty());
    // Output voltage regulation percentage
    ctx.push_obligation(ProofObligation::assume("rp", "reg_pct == 5"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_reg_pct == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "reg_ok == if reg_pct <= max_reg_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "reg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo harvester: 5% regulation ≤ 10% max → OK");
}

#[test]
fn frequency_bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_hz", "min_bw_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Usable frequency bandwidth around resonance
    ctx.push_obligation(ProofObligation::assume("bh", "bw_hz == 10"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bw_hz == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_hz >= min_bw_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo harvester: 10Hz bandwidth ≥ 5Hz min → OK");
}

#[test]
fn output_duty_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["duty_pct", "min_duty_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("duty_ok", i32_ty());
    // Duty cycle of intermittent operation
    ctx.push_obligation(ProofObligation::assume("dp", "duty_pct == 30"));
    ctx.push_obligation(ProofObligation::assume("md", "min_duty_pct == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "duty_ok == if duty_pct >= min_duty_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "duty_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Piezo harvester: 30% duty ≥ 10% min → OK");
}
