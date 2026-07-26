// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn load_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["load_v", "max_load_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("volt_ok", i32_ty());
    // Maximum blocking voltage
    ctx.push_obligation(ProofObligation::assume("lv", "load_v == 240"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_load_v == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "volt_ok == if load_v <= max_load_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "volt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SSR: 240V load ≤ 600V max → OK");
}

#[test]
fn load_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_a", "max_current_a"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cur_ok", i32_ty());
    // Continuous load current
    ctx.push_obligation(ProofObligation::assume("ca", "current_a == 25"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_a == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cur_ok == if current_a <= max_current_a { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cur_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SSR: 25A load ≤ 100A max → OK");
}

#[test]
fn switching_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sw_type", u32_ty());
    ctx.declare_var_typed("valid_sw", i32_ty());
    // Switching types: 1=zero-cross, 2=random/instant-on, 3=peak-switching, 4=phase-angle
    ctx.push_obligation(ProofObligation::assume("st", "sw_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_sw == if sw_type == 1 || sw_type == 2 || sw_type == 3 || sw_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_sw == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SSR: zero-cross is valid switching type");
}

#[test]
fn on_state_voltage_drop() {
    let mut ctx = VerificationContext::new();
    for v in &["vdrop_mv", "max_vdrop_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vd_ok", i32_ty());
    // On-state voltage drop in mV (TRIAC/SCR forward drop)
    ctx.push_obligation(ProofObligation::assume("vm", "vdrop_mv == 1200")); // 1.2V
    ctx.push_obligation(ProofObligation::assume("mv", "max_vdrop_mv == 1800")); // 1.8V max
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vd_ok == if vdrop_mv <= max_vdrop_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SSR: 1.2V on-state drop ≤ 1.8V max → OK");
}

#[test]
fn control_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["ctrl_mv", "min_ctrl_mv", "max_ctrl_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ctrl_ok", i32_ty());
    // Control input voltage range in mV
    ctx.push_obligation(ProofObligation::assume("cm", "ctrl_mv == 5000")); // 5V DC
    ctx.push_obligation(ProofObligation::assume("mn", "min_ctrl_mv == 3000")); // 3V min
    ctx.push_obligation(ProofObligation::assume("mx", "max_ctrl_mv == 32000")); // 32V max
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "ctrl_ok == if ctrl_mv >= min_ctrl_mv && ctrl_mv <= max_ctrl_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ctrl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SSR: 5V control in [3, 32] → OK");
}

#[test]
fn leakage_current() {
    let mut ctx = VerificationContext::new();
    for v in &["leakage_ua", "max_leakage_ua"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("leak_ok", i32_ty());
    // Off-state leakage current in μA
    ctx.push_obligation(ProofObligation::assume("lu", "leakage_ua == 500")); // 0.5mA
    ctx.push_obligation(ProofObligation::assume("ml", "max_leakage_ua == 5000")); // 5mA
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "leak_ok == if leakage_ua <= max_leakage_ua { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "leak_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SSR: 0.5mA leakage ≤ 5mA max → OK");
}

#[test]
fn output_device() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("device", u32_ty());
    ctx.declare_var_typed("valid_dev", i32_ty());
    // Output semiconductor: 1=TRIAC, 2=SCR (back-to-back), 3=MOSFET, 4=IGBT
    ctx.push_obligation(ProofObligation::assume("d", "device == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_dev == if device == 1 || device == 2 || device == 3 || device == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_dev == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SSR: TRIAC is valid output device");
}

#[test]
fn surge_current() {
    let mut ctx = VerificationContext::new();
    for v in &["surge_a", "max_surge_a"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("surge_ok", i32_ty());
    // Non-repetitive surge current (1 cycle)
    ctx.push_obligation(ProofObligation::assume("sa", "surge_a == 300"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_surge_a == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "surge_ok == if surge_a <= max_surge_a { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "surge_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SSR: 300A surge ≤ 1000A max → OK");
}

#[test]
fn thermal_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["rth_x10", "max_rth_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rth_ok", i32_ty());
    // Thermal resistance °C/W (×10 for 0.1°C/W)
    ctx.push_obligation(ProofObligation::assume("rx", "rth_x10 == 12")); // 1.2°C/W
    ctx.push_obligation(ProofObligation::assume("mr", "max_rth_x10 == 30")); // 3.0°C/W
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rth_ok == if rth_x10 <= max_rth_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SSR: 1.2°C/W thermal resistance ≤ 3.0 max → OK");
}

#[test]
fn isolation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["iso_vrms", "min_iso_vrms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("iso_ok", i32_ty());
    // Input-to-output isolation voltage Vrms
    ctx.push_obligation(ProofObligation::assume("iv", "iso_vrms == 4000"));
    ctx.push_obligation(ProofObligation::assume("mi", "min_iso_vrms == 2500"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "iso_ok == if iso_vrms >= min_iso_vrms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "iso_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SSR: 4000 Vrms isolation ≥ 2500 min → OK");
}
