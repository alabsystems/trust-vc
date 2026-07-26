// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn temperature_differential() {
    let mut ctx = VerificationContext::new();
    for v in &["hot_side_c_x10", "cold_side_c_x10", "delta_t_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // ΔT = Thot - Tcold (×10 for 0.1°C resolution, offset +500 for signed)
    // Hot=55.0°C(1050), Cold=25.0°C(750) → ΔT=30.0°C(300)
    ctx.push_obligation(ProofObligation::assume("hs", "hot_side_c_x10 == 1050")); // 55.0°C + 500
    ctx.push_obligation(ProofObligation::assume("cs", "cold_side_c_x10 == 750")); // 25.0°C + 500
    ctx.push_obligation(ProofObligation::assume(
        "dt",
        "delta_t_x10 == hot_side_c_x10 - cold_side_c_x10",
    ));
    ctx.push_obligation(ProofObligation::assert("is_300", "delta_t_x10 == 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEC: 55°C hot - 25°C cold = 30°C differential");
}

#[test]
fn max_delta_t() {
    let mut ctx = VerificationContext::new();
    for v in &["delta_t_x10", "max_delta_t_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("delta_ok", i32_ty());
    // Typical max ΔT: 60-70°C for single-stage TEC
    ctx.push_obligation(ProofObligation::assume("dt", "delta_t_x10 == 300")); // 30.0°C
    ctx.push_obligation(ProofObligation::assume("md", "max_delta_t_x10 == 670")); // 67.0°C
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "delta_ok == if delta_t_x10 <= max_delta_t_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "delta_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEC: ΔT 30°C ≤ 67°C max → within capability");
}

#[test]
fn drive_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ma", "max_current_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("current_ok", i32_ty());
    // TEC drive current (Imax typically 3-8A depending on module)
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma == 4000")); // 4.0A
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_ma == 6000")); // 6.0A
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "current_ok == if current_ma <= max_current_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEC: 4.0A drive ≤ 6.0A max → current OK");
}

#[test]
fn voltage_supply() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "max_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voltage_ok", i32_ty());
    // TEC Vmax: typically 8-16V depending on module
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 12000")); // 12V
    ctx.push_obligation(ProofObligation::assume("mv", "max_voltage_mv == 15400")); // 15.4V
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "voltage_ok == if supply_mv <= max_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "voltage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEC: 12V supply ≤ 15.4V max → voltage OK");
}

#[test]
fn cooling_power() {
    let mut ctx = VerificationContext::new();
    for v in &["heat_load_mw", "qmax_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cooling_ok", i32_ty());
    // Cooling capacity (Qmax) must exceed heat load
    ctx.push_obligation(ProofObligation::assume("hl", "heat_load_mw == 30000")); // 30W
    ctx.push_obligation(ProofObligation::assume("qm", "qmax_mw == 50000")); // 50W
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cooling_ok == if heat_load_mw <= qmax_mw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cooling_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEC: 30W load ≤ 50W Qmax → cooling sufficient");
}

#[test]
fn cop_efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["qc_mw", "power_in_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cop_x100", u32_ty());
    // COP = Qc/Pin. Precompute: 30000/48000 × 100 = 62 (0.62)
    ctx.push_obligation(ProofObligation::assume("qc", "qc_mw == 30000"));
    ctx.push_obligation(ProofObligation::assume("pi", "power_in_mw == 48000"));
    ctx.push_obligation(ProofObligation::assume("cop", "cop_x100 == 62")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_62", "cop_x100 == 62"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEC: COP = 30W/48W = 0.62 (precomputed)");
}

#[test]
fn cascade_stages() {
    let mut ctx = VerificationContext::new();
    for v in &["stages", "max_stages"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stages_ok", i32_ty());
    // Cascaded (multi-stage) TECs: 1-4 stages typical
    ctx.push_obligation(ProofObligation::assume("s", "stages == 2"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_stages == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "stages_ok == if stages <= max_stages { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stages_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEC: 2 stages ≤ 4 max → cascade OK");
}

#[test]
fn pwm_control() {
    let mut ctx = VerificationContext::new();
    for v in &["duty_pct", "max_duty_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("duty_ok", i32_ty());
    // PWM duty cycle for TEC drive
    ctx.push_obligation(ProofObligation::assume("dp", "duty_pct == 65"));
    ctx.push_obligation(ProofObligation::assume("md", "max_duty_pct == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "duty_ok == if duty_pct <= max_duty_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "duty_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEC: 65% PWM duty ≤ 100% max → OK");
}

#[test]
fn hot_side_heatsink() {
    let mut ctx = VerificationContext::new();
    for v in &["hot_side_c_x10", "max_hot_c_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("heatsink_ok", i32_ty());
    // Hot side must stay below Tmax (typically 80°C) with heatsink. Offset +500.
    ctx.push_obligation(ProofObligation::assume("hs", "hot_side_c_x10 == 1050")); // 55.0°C
    ctx.push_obligation(ProofObligation::assume("mh", "max_hot_c_x10 == 1300")); // 80.0°C
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "heatsink_ok == if hot_side_c_x10 <= max_hot_c_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "heatsink_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEC: hot side 55°C ≤ 80°C max → heatsink adequate");
}

#[test]
fn polarity_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polarity", u32_ty());
    ctx.declare_var_typed("is_cooling", i32_ty());
    // Polarity: 0=cooling, 1=heating (reverse current)
    ctx.push_obligation(ProofObligation::assume("p", "polarity == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ic_def",
        "is_cooling == if polarity == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_cooling == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEC: polarity=0 → cooling mode");
}
