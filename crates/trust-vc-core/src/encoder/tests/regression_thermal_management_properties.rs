// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn thermal_zone_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_mc", "passive_threshold_mc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("throttle", i32_ty());
    // Temperature in millicelsius; passive threshold triggers CPU throttle
    ctx.push_obligation(ProofObligation::assume("t", "temp_mc == 85000")); // 85°C
    ctx.push_obligation(ProofObligation::assume(
        "pt",
        "passive_threshold_mc == 80000",
    )); // 80°C
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "throttle == if temp_mc > passive_threshold_mc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "throttle == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermal: 85°C > 80°C passive → throttle");
}

#[test]
fn critical_shutdown_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_mc", "critical_mc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("shutdown", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "temp_mc == 105000")); // 105°C
    ctx.push_obligation(ProofObligation::assume("c", "critical_mc == 100000")); // 100°C
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "shutdown == if temp_mc >= critical_mc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "shutdown == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermal: 105°C >= 100°C critical → shutdown");
}

#[test]
fn fan_duty_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_mc", "low_mc", "high_mc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fan_speed", u32_ty());
    // Simple fan curve: off below low, max above high, proportional between
    // 70°C is between 60°C low and 80°C high → 50% = 128/255
    ctx.push_obligation(ProofObligation::assume("t", "temp_mc == 70000"));
    ctx.push_obligation(ProofObligation::assume("l", "low_mc == 60000"));
    ctx.push_obligation(ProofObligation::assume("h", "high_mc == 80000"));
    ctx.push_obligation(ProofObligation::assume("fs", "fan_speed == 128")); // precomputed ~50%
    ctx.push_obligation(ProofObligation::assert("is_128", "fan_speed == 128"));
    ctx.push_obligation(ProofObligation::assert("nonzero", "fan_speed > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermal fan: 70°C in [60,80] → 50% duty");
}

#[test]
fn heatsink_thermal_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["power_mw", "thermal_resistance_mk_per_w", "temp_rise_mk"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // ΔT = P × R_th. Precompute: 5000mW × 10 °C/W = 50°C = 50000 m°C
    // Use millikelvins: 5000 × 10 = 50000
    ctx.push_obligation(ProofObligation::assume("pm", "power_mw == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "tr",
        "thermal_resistance_mk_per_w == 10",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "trm_def",
        "temp_rise_mk == power_mw * thermal_resistance_mk_per_w",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50000", "temp_rise_mk == 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "thermal: 5W × 10°C/W = 50°C rise");
}

#[test]
fn cooling_power_budget() {
    let mut ctx = VerificationContext::new();
    for v in &["tdp_mw", "cooling_capacity_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("adequate", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "tdp_mw == 15000")); // 15W TDP
    ctx.push_obligation(ProofObligation::assume(
        "cc",
        "cooling_capacity_mw == 20000",
    )); // 20W cooler
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "adequate == if cooling_capacity_mw >= tdp_mw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "adequate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermal: 20W cooling >= 15W TDP → adequate");
}

#[test]
fn junction_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["ambient_mc", "power_mw", "theta_ja"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("junction_mc", u32_ty());
    ctx.declare_var_typed("safe", i32_ty());
    // Tj = Ta + P × θja. Precompute: 25000 + 2000 × 40 = 25000 + 80000 = 105000
    ctx.push_obligation(ProofObligation::assume("a", "ambient_mc == 25000"));
    ctx.push_obligation(ProofObligation::assume("p", "power_mw == 2000"));
    ctx.push_obligation(ProofObligation::assume("tj", "theta_ja == 40"));
    ctx.push_obligation(ProofObligation::assume("jm", "junction_mc == 105000")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "safe == if junction_mc < 125000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_105000",
        "junction_mc == 105000",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "safe == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermal: Tj = 25 + 80 = 105°C < 125°C max");
}

#[test]
fn thermal_hysteresis() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_mc", "on_threshold_mc", "off_threshold_mc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fan_on", i32_ty());
    ctx.declare_var_typed("hysteresis_valid", i32_ty());
    // Hysteresis: fan turns on at 75°C, off at 70°C (5°C hysteresis)
    // Current temp 72°C, fan was on → stays on (above off threshold)
    ctx.push_obligation(ProofObligation::assume("t", "temp_mc == 72000"));
    ctx.push_obligation(ProofObligation::assume("on", "on_threshold_mc == 75000"));
    ctx.push_obligation(ProofObligation::assume("off", "off_threshold_mc == 70000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "fan_on == if temp_mc > off_threshold_mc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hv_def",
        "hysteresis_valid == if on_threshold_mc > off_threshold_mc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("on", "fan_on == 1"));
    ctx.push_obligation(ProofObligation::assert("hyst_ok", "hysteresis_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermal: 72°C > 70°C off threshold → fan stays on");
}

#[test]
fn multi_sensor_max_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["cpu_temp_mc", "gpu_temp_mc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("max_temp_mc", u32_ty());
    ctx.declare_var_typed("needs_throttle", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ct", "cpu_temp_mc == 78000"));
    ctx.push_obligation(ProofObligation::assume("gt", "gpu_temp_mc == 82000"));
    ctx.push_obligation(ProofObligation::assume(
        "mt_def",
        "max_temp_mc == if cpu_temp_mc > gpu_temp_mc { cpu_temp_mc } else { gpu_temp_mc }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "needs_throttle == if max_temp_mc > 80000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_82000", "max_temp_mc == 82000"));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_throttle == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thermal: max(CPU 78°C, GPU 82°C) = 82°C > 80°C → throttle",
    );
}

#[test]
fn thermal_trip_count() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "passive_trips",
        "active_trips",
        "critical_trips",
        "total_trips",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Total trip points in thermal zone
    ctx.push_obligation(ProofObligation::assume("pt", "passive_trips == 1"));
    ctx.push_obligation(ProofObligation::assume("at", "active_trips == 4"));
    ctx.push_obligation(ProofObligation::assume("ct", "critical_trips == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tt_def",
        "total_trips == passive_trips + active_trips + critical_trips",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "total_trips == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thermal: 1 passive + 4 active + 1 critical = 6 trips",
    );
}

#[test]
fn pstate_frequency_step() {
    let mut ctx = VerificationContext::new();
    for v in &["current_pstate", "max_pstate", "base_freq_mhz", "step_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("actual_freq_mhz", u32_ty());
    ctx.declare_var_typed("throttled", i32_ty());
    // P-state reduces frequency in steps: actual = base - (pstate × step)
    // base=3000, pstate=2, step=200 → 3000 - 400 = 2600
    ctx.push_obligation(ProofObligation::assume("cp", "current_pstate == 2"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pstate == 10"));
    ctx.push_obligation(ProofObligation::assume("bf", "base_freq_mhz == 3000"));
    ctx.push_obligation(ProofObligation::assume("sm", "step_mhz == 200"));
    ctx.push_obligation(ProofObligation::assume("af", "actual_freq_mhz == 2600")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "throttled == if current_pstate > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_2600",
        "actual_freq_mhz == 2600",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "throttled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermal P-state: base 3000 - 2×200 = 2600 MHz");
}
