// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn microstep_resolution() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("microstep_setting", u32_ty());
    ctx.declare_var_typed("is_valid", i32_ty());
    // Valid microstep: 1, 2, 4, 8, 16, 32, 64, 128, 256
    // Check power of 2 via common values
    ctx.push_obligation(ProofObligation::assume("ms", "microstep_setting == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "is_valid == if microstep_setting == 1 || microstep_setting == 2 || microstep_setting == 4 || microstep_setting == 8 || microstep_setting == 16 || microstep_setting == 32 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper IC: 1/16 microstep → valid resolution");
}

#[test]
fn current_limit_setting() {
    let mut ctx = VerificationContext::new();
    for v in &["vref_mv", "sense_resistor_mohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("current_limit_ma", u32_ty());
    // I_limit = VREF / R_sense. Precompute: 500mV / 200mΩ = 2500mA
    ctx.push_obligation(ProofObligation::assume("vm", "vref_mv == 500"));
    ctx.push_obligation(ProofObligation::assume("sr", "sense_resistor_mohm == 200"));
    ctx.push_obligation(ProofObligation::assume("cl", "current_limit_ma == 2500")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_2500",
        "current_limit_ma == 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper IC: 500mV / 0.2Ω = 2.5A limit (precomputed)",
    );
}

#[test]
fn decay_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("decay_setting", u32_ty());
    ctx.declare_var_typed("is_mixed", i32_ty());
    // Decay: 0=slow, 1=fast, 2=mixed
    ctx.push_obligation(ProofObligation::assume("ds", "decay_setting == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "im_def",
        "is_mixed == if decay_setting == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_mixed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper IC: decay 2 → mixed decay mode");
}

#[test]
fn thermal_warning() {
    let mut ctx = VerificationContext::new();
    for v in &["die_temp_c", "warning_temp_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tw_active", i32_ty());
    // Thermal warning typically at 120°C, shutdown at 150°C
    ctx.push_obligation(ProofObligation::assume("dt", "die_temp_c == 130"));
    ctx.push_obligation(ProofObligation::assume("wt", "warning_temp_c == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "tw_def",
        "tw_active == if die_temp_c >= warning_temp_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tw_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper IC: 130°C ≥ 120°C warning → thermal warning active",
    );
}

#[test]
fn step_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["step_freq_hz", "max_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Max step frequency depends on driver IC
    ctx.push_obligation(ProofObligation::assume("sf", "step_freq_hz == 50000"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_freq_hz == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if step_freq_hz <= max_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper IC: 50kHz ≤ 100kHz max → frequency OK");
}

#[test]
fn supply_voltage_range() {
    let mut ctx = VerificationContext::new();
    for v in &["vm_mv", "min_vm_mv", "max_vm_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vm_ok", i32_ty());
    // Motor supply: e.g., 8-45V
    ctx.push_obligation(ProofObligation::assume("vm", "vm_mv == 24000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_vm_mv == 8000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_vm_mv == 45000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vm_ok == if vm_mv >= min_vm_mv && vm_mv <= max_vm_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vm_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper IC: 24V in [8, 45] → motor supply OK");
}

#[test]
fn stall_detection_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["load_value", "stall_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("stall_flag", i32_ty());
    // StallGuard: load value drops below threshold
    ctx.push_obligation(ProofObligation::assume("lv", "load_value == 50"));
    ctx.push_obligation(ProofObligation::assume("st", "stall_threshold == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "sf_def",
        "stall_flag == if load_value < stall_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "stall_flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper IC: load 50 < 100 threshold → stall detected",
    );
}

#[test]
fn coolstep_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_scale", "min_scale", "max_scale"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("scale_ok", i32_ty());
    // CoolStep: dynamic current scaling 1/32 to 32/32
    ctx.push_obligation(ProofObligation::assume("cs", "current_scale == 16"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_scale == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_scale == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "scale_ok == if current_scale >= min_scale && current_scale <= max_scale { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "scale_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Stepper IC: scale 16 in [1, 32] → CoolStep OK");
}

#[test]
fn blanking_time() {
    let mut ctx = VerificationContext::new();
    for v in &["blank_ns", "min_blank_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("blank_ok", i32_ty());
    // Comparator blanking time: ignore noise after switching
    ctx.push_obligation(ProofObligation::assume("bn", "blank_ns == 1000")); // 1μs
    ctx.push_obligation(ProofObligation::assume("mb", "min_blank_ns == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "blank_ok == if blank_ns >= min_blank_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "blank_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper IC: 1000ns blank ≥ 500ns min → blanking OK",
    );
}

#[test]
fn chopper_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["chop_freq_khz", "min_chop_khz", "max_chop_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("chop_ok", i32_ty());
    // Chopper frequency: 20-50 kHz typical
    ctx.push_obligation(ProofObligation::assume("cf", "chop_freq_khz == 30"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_chop_khz == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_chop_khz == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "chop_ok == if chop_freq_khz >= min_chop_khz && chop_freq_khz <= max_chop_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "chop_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Stepper IC: 30kHz chop in [20, 50] → chopper freq OK",
    );
}
