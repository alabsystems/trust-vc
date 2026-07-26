// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn temperature_differential() {
    let mut ctx = VerificationContext::new();
    for v in &["delta_t_x10", "min_delta_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dt_ok", i32_ty());
    // Temperature differential hot-cold side (×10 for 0.1°C)
    ctx.push_obligation(ProofObligation::assume("dx", "delta_t_x10 == 500")); // 50.0°C
    ctx.push_obligation(ProofObligation::assume("md", "min_delta_x10 == 100")); // 10.0°C
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dt_ok == if delta_t_x10 >= min_delta_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEG: 50.0°C ΔT ≥ 10.0°C min → OK");
}

#[test]
fn output_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vout_mv", "min_vout_mv", "max_vout_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vout_ok", i32_ty());
    // TEG output voltage in millivolts
    ctx.push_obligation(ProofObligation::assume("vm", "vout_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vout_mv == 500"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vout_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vout_ok == if vout_mv >= min_vout_mv && vout_mv <= max_vout_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vout_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEG: 3.3V output in [0.5, 12.0] → OK");
}

#[test]
fn power_output() {
    let mut ctx = VerificationContext::new();
    for v in &["power_mw", "min_power_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pwr_ok", i32_ty());
    // TEG electrical power output
    ctx.push_obligation(ProofObligation::assume("pm", "power_mw == 500"));
    ctx.push_obligation(ProofObligation::assume("mp", "min_power_mw == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pwr_ok == if power_mw >= min_power_mw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pwr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEG: 500mW power ≥ 100mW min → OK");
}

#[test]
fn element_count() {
    let mut ctx = VerificationContext::new();
    for v in &["couples", "min_couples", "max_couples"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("elem_ok", i32_ty());
    // Number of thermoelectric couples
    ctx.push_obligation(ProofObligation::assume("c", "couples == 127"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_couples == 32"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_couples == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "elem_ok == if couples >= min_couples && couples <= max_couples { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "elem_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEG: 127 couples in [32, 256] → OK");
}

#[test]
fn hot_side_temp() {
    let mut ctx = VerificationContext::new();
    for v in &["hot_temp_c", "max_hot_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hot_ok", i32_ty());
    // Maximum hot side temperature in °C
    ctx.push_obligation(ProofObligation::assume("hc", "hot_temp_c == 200"));
    ctx.push_obligation(ProofObligation::assume("mh", "max_hot_c == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hot_ok == if hot_temp_c <= max_hot_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hot_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEG: 200°C hot side ≤ 300°C max → OK");
}

#[test]
fn internal_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["resistance_mohm", "max_resistance_mohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Internal resistance in milliohms
    ctx.push_obligation(ProofObligation::assume("rm", "resistance_mohm == 1500")); // 1.5Ω
    ctx.push_obligation(ProofObligation::assume("mr", "max_resistance_mohm == 5000")); // 5.0Ω
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if resistance_mohm <= max_resistance_mohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEG: 1.5Ω internal resistance ≤ 5.0Ω max → OK");
}

#[test]
fn figure_of_merit() {
    let mut ctx = VerificationContext::new();
    for v in &["zt_x1000", "min_zt_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("zt_ok", i32_ty());
    // Figure of merit ZT (×1000 for 0.001 precision)
    ctx.push_obligation(ProofObligation::assume("zx", "zt_x1000 == 800")); // 0.800
    ctx.push_obligation(ProofObligation::assume("mz", "min_zt_x1000 == 500")); // 0.500
    ctx.push_obligation(ProofObligation::assume(
        "zo_def",
        "zt_ok == if zt_x1000 >= min_zt_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "zt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEG: ZT 0.800 ≥ 0.500 min → OK");
}

#[test]
fn seebeck_coefficient() {
    let mut ctx = VerificationContext::new();
    for v in &["seebeck_uv_per_k", "min_seebeck", "max_seebeck"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("see_ok", i32_ty());
    // Seebeck coefficient in μV/K
    ctx.push_obligation(ProofObligation::assume("su", "seebeck_uv_per_k == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_seebeck == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_seebeck == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "see_ok == if seebeck_uv_per_k >= min_seebeck && seebeck_uv_per_k <= max_seebeck { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "see_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEG: 200 μV/K Seebeck in [100, 500] → OK");
}

#[test]
fn module_efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["efficiency_x10", "min_eff_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("eff_ok", i32_ty());
    // Conversion efficiency in % (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("ex", "efficiency_x10 == 55")); // 5.5%
    ctx.push_obligation(ProofObligation::assume("me", "min_eff_x10 == 30")); // 3.0%
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "eff_ok == if efficiency_x10 >= min_eff_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "eff_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEG: 5.5% efficiency ≥ 3.0% min → OK");
}

#[test]
fn thermal_cycling() {
    let mut ctx = VerificationContext::new();
    for v in &["cycles", "min_cycles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cyc_ok", i32_ty());
    // Thermal cycling endurance
    ctx.push_obligation(ProofObligation::assume("c", "cycles == 10000"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_cycles == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cyc_ok == if cycles >= min_cycles { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cyc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TEG: 10000 thermal cycles ≥ 5000 min → OK");
}
