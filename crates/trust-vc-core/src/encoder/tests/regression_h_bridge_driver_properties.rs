// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn shoot_through_prevention() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("high_side", u32_ty());
    ctx.declare_var_typed("low_side", u32_ty());
    ctx.declare_var_typed("no_shoot_through", i32_ty());
    // Both high and low side ON simultaneously = shoot-through (forbidden)
    ctx.push_obligation(ProofObligation::assume("hs", "high_side == 1"));
    ctx.push_obligation(ProofObligation::assume("ls", "low_side == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "no_shoot_through == if high_side == 0 || low_side == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "no_shoot_through == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "H-bridge: high=1, low=0 → no shoot-through");
}

#[test]
fn dead_time() {
    let mut ctx = VerificationContext::new();
    for v in &["dead_time_ns", "min_dead_time_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dt_ok", i32_ty());
    // Dead time between switching: prevents shoot-through
    ctx.push_obligation(ProofObligation::assume("dt", "dead_time_ns == 500"));
    ctx.push_obligation(ProofObligation::assume("md", "min_dead_time_ns == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dt_ok == if dead_time_ns >= min_dead_time_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "H-bridge: 500ns dead time ≥ 200ns min → dead time OK",
    );
}

#[test]
fn voltage_rating() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "max_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voltage_ok", i32_ty());
    // MOSFET Vds rating must exceed supply
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 24000"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_voltage_mv == 40000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "voltage_ok == if supply_mv <= max_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "voltage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "H-bridge: 24V supply ≤ 40V rating → voltage OK");
}

#[test]
fn rds_on_power() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "rds_on_mohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("power_loss_mw", u32_ty());
    // P_loss = I² × Rds(on). Precompute: (5000mA)² × 50mΩ / 1000000 = 1250mW
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma == 5000"));
    ctx.push_obligation(ProofObligation::assume("ro", "rds_on_mohm == 50"));
    ctx.push_obligation(ProofObligation::assume("pl", "power_loss_mw == 1250")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1250", "power_loss_mw == 1250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "H-bridge: 5A² × 50mΩ = 1.25W loss (precomputed)");
}

#[test]
fn pwm_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["pwm_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // MOSFET H-bridge PWM: typically 10-100 kHz
    ctx.push_obligation(ProofObligation::assume("pf", "pwm_freq_khz == 20"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_freq_khz == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if pwm_freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "H-bridge: 20 kHz ≤ 100 kHz max → PWM freq OK");
}

#[test]
fn gate_drive_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["gate_voltage_mv", "min_gate_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fully_enhanced", i32_ty());
    // Gate voltage must exceed Vgs(th) for full enhancement
    ctx.push_obligation(ProofObligation::assume("gv", "gate_voltage_mv == 10000"));
    ctx.push_obligation(ProofObligation::assume("mg", "min_gate_mv == 4500")); // Vgs(th)
    ctx.push_obligation(ProofObligation::assume(
        "fe_def",
        "fully_enhanced == if gate_voltage_mv >= min_gate_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fully_enhanced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "H-bridge: 10V gate ≥ 4.5V Vgs(th) → fully enhanced",
    );
}

#[test]
fn bootstrap_capacitor() {
    let mut ctx = VerificationContext::new();
    for v in &["cap_nf", "min_cap_nf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cap_ok", i32_ty());
    // Bootstrap cap for high-side gate drive
    ctx.push_obligation(ProofObligation::assume("cn", "cap_nf == 100"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_cap_nf == 47"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cap_ok == if cap_nf >= min_cap_nf { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "H-bridge: 100nF bootstrap ≥ 47nF min → cap OK");
}

#[test]
fn current_sense() {
    let mut ctx = VerificationContext::new();
    for v in &["sense_mv", "overcurrent_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("oc_fault", i32_ty());
    // Current sense resistor: V = I × R_sense
    ctx.push_obligation(ProofObligation::assume("sm", "sense_mv == 600"));
    ctx.push_obligation(ProofObligation::assume("om", "overcurrent_mv == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "of_def",
        "oc_fault == if sense_mv >= overcurrent_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "oc_fault == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "H-bridge: 600mV sense ≥ 500mV OC → overcurrent fault",
    );
}

#[test]
fn thermal_shutdown() {
    let mut ctx = VerificationContext::new();
    for v in &["junction_temp_c", "shutdown_temp_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("shutdown", i32_ty());
    // Thermal shutdown: typically 150-175°C
    ctx.push_obligation(ProofObligation::assume("jt", "junction_temp_c == 160"));
    ctx.push_obligation(ProofObligation::assume("st", "shutdown_temp_c == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "shutdown == if junction_temp_c >= shutdown_temp_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "shutdown == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "H-bridge: 160°C ≥ 150°C threshold → thermal shutdown",
    );
}

#[test]
fn flyback_diode() {
    let mut ctx = VerificationContext::new();
    for v in &["diode_voltage_v", "supply_voltage_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("diode_ok", i32_ty());
    // Body diode or external flyback must handle supply voltage
    ctx.push_obligation(ProofObligation::assume("dv", "diode_voltage_v == 40"));
    ctx.push_obligation(ProofObligation::assume("sv", "supply_voltage_v == 24"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "diode_ok == if diode_voltage_v >= supply_voltage_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "diode_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "H-bridge: 40V diode ≥ 24V supply → flyback OK");
}
