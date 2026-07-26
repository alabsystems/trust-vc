// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flash_energy() {
    let mut ctx = VerificationContext::new();
    for v in &["mj", "mj_min", "mj_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Flash energy in mJ (millijoules): value 5000, valid range 1 to 100000
    ctx.push_obligation(ProofObligation::assume("fe_val", "mj == 5000"));
    ctx.push_obligation(ProofObligation::assume("fe_min", "mj_min == 1"));
    ctx.push_obligation(ProofObligation::assume("fe_max", "mj_max == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "fe_in_range",
        "mj >= mj_min && mj <= mj_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flash energy 5000 mJ in range [1,100000]");
}

#[test]
fn repetition_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["hz", "hz_min", "hz_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Repetition rate in Hz: value 50, valid range 1 to 1000
    ctx.push_obligation(ProofObligation::assume("rr_val", "hz == 50"));
    ctx.push_obligation(ProofObligation::assume("rr_min", "hz_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rr_max", "hz_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "rr_in_range",
        "hz >= hz_min && hz <= hz_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repetition rate 50 Hz in range [1,1000]");
}

#[test]
fn pulse_duration() {
    let mut ctx = VerificationContext::new();
    for v in &["us", "us_min", "us_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pulse duration in microseconds: value 1200, valid range 1 to 50000
    ctx.push_obligation(ProofObligation::assume("pd_val", "us == 1200"));
    ctx.push_obligation(ProofObligation::assume("pd_min", "us_min == 1"));
    ctx.push_obligation(ProofObligation::assume("pd_max", "us_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "pd_in_range",
        "us >= us_min && us <= us_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulse duration 1200 us in range [1,50000]");
}

#[test]
fn trigger_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trigger", u32_ty());
    ctx.declare_var_typed("valid_trigger", i32_ty());
    // 1=external trigger, 2=internal oscillator, 3=simmer mode
    ctx.push_obligation(ProofObligation::assume("tm_val", "trigger == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tm_valid_def",
        "valid_trigger == if trigger == 1 || trigger == 2 || trigger == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tm_check", "valid_trigger == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trigger mode 1 (external trigger) is valid");
}

#[test]
fn lamp_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["volts", "volts_min", "volts_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Lamp voltage in V DC: value 800, valid range 100 to 2000
    ctx.push_obligation(ProofObligation::assume("lv_val", "volts == 800"));
    ctx.push_obligation(ProofObligation::assume("lv_min", "volts_min == 100"));
    ctx.push_obligation(ProofObligation::assume("lv_max", "volts_max == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "lv_in_range",
        "volts >= volts_min && volts <= volts_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lamp voltage 800 V DC in range [100,2000]");
}

#[test]
fn arc_length() {
    let mut ctx = VerificationContext::new();
    for v in &["mm", "mm_min", "mm_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Arc length in mm: value 75, valid range 1 to 300
    ctx.push_obligation(ProofObligation::assume("al_val", "mm == 75"));
    ctx.push_obligation(ProofObligation::assume("al_min", "mm_min == 1"));
    ctx.push_obligation(ProofObligation::assume("al_max", "mm_max == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "al_in_range",
        "mm >= mm_min && mm <= mm_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "arc length 75 mm in range [1,300]");
}

#[test]
fn color_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["kelvin", "kelvin_min", "kelvin_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Color temperature in Kelvin: value 6500, valid range 3000 to 10000
    ctx.push_obligation(ProofObligation::assume("ct_val", "kelvin == 6500"));
    ctx.push_obligation(ProofObligation::assume("ct_min", "kelvin_min == 3000"));
    ctx.push_obligation(ProofObligation::assume("ct_max", "kelvin_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "ct_in_range",
        "kelvin >= kelvin_min && kelvin <= kelvin_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "color temperature 6500 K in range [3000,10000]");
}

#[test]
fn lamp_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lamp", u32_ty());
    ctx.declare_var_typed("valid_lamp", i32_ty());
    // 1=linear, 2=U-shaped, 3=spiral, 4=ring
    ctx.push_obligation(ProofObligation::assume("lt_val", "lamp == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "lt_valid_def",
        "valid_lamp == if lamp == 1 || lamp == 2 || lamp == 3 || lamp == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("lt_check", "valid_lamp == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lamp type 2 (U-shaped) is valid");
}

#[test]
fn cooling_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", u32_ty());
    ctx.declare_var_typed("valid_cooling", i32_ty());
    // 1=convection, 2=forced air, 3=liquid
    ctx.push_obligation(ProofObligation::assume("cy_val", "cooling == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "cy_valid_def",
        "valid_cooling == if cooling == 1 || cooling == 2 || cooling == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cy_check", "valid_cooling == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling type 3 (liquid) is valid");
}

#[test]
fn simmer_current() {
    let mut ctx = VerificationContext::new();
    for v in &["ma", "ma_min", "ma_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Simmer current in mA: value 200, valid range 10 to 5000
    ctx.push_obligation(ProofObligation::assume("sc_val", "ma == 200"));
    ctx.push_obligation(ProofObligation::assume("sc_min", "ma_min == 10"));
    ctx.push_obligation(ProofObligation::assume("sc_max", "ma_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "sc_in_range",
        "ma >= ma_min && ma <= ma_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "simmer current 200 mA in range [10,5000]");
}
