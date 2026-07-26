// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn turns_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["primary_amps", "secondary_ma", "turns_ratio"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // I_secondary = I_primary / N. Precompute: 100A / 2000 turns × 1000 = 50mA
    ctx.push_obligation(ProofObligation::assume("pa", "primary_amps == 100"));
    ctx.push_obligation(ProofObligation::assume("tr", "turns_ratio == 2000"));
    ctx.push_obligation(ProofObligation::assume("sm", "secondary_ma == 50")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_50", "secondary_ma == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CT: 100A / 2000:1 = 50mA secondary (precomputed)");
}

#[test]
fn burden_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["burden_ohms", "max_burden_ohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("burden_ok", i32_ty());
    // Burden must not exceed rated VA / I²
    ctx.push_obligation(ProofObligation::assume("bo", "burden_ohms == 10"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_burden_ohms == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "burden_ok == if burden_ohms <= max_burden_ohms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "burden_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CT: 10Ω burden ≤ 20Ω max → burden OK");
}

#[test]
fn accuracy_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_pct_x10", u32_ty());
    ctx.declare_var_typed("is_metering", i32_ty());
    // Metering CTs: 0.1%, 0.2%, 0.5%, 1.0%. In ×10: 1, 2, 5, 10
    ctx.push_obligation(ProofObligation::assume("ap", "accuracy_pct_x10 == 2")); // 0.2%
    ctx.push_obligation(ProofObligation::assume(
        "im_def",
        "is_metering == if accuracy_pct_x10 <= 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_metering == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CT: 0.2% accuracy ≤ 1.0% → metering class");
}

#[test]
fn saturation_check() {
    let mut ctx = VerificationContext::new();
    for v in &["primary_amps", "rated_amps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("saturated", i32_ty());
    // CT saturates above rated current × ALF (accuracy limit factor)
    // ALF=20 for protection, rated=5A → saturation at 100A
    ctx.push_obligation(ProofObligation::assume("pa", "primary_amps == 120"));
    ctx.push_obligation(ProofObligation::assume("ra", "rated_amps == 100")); // precomputed ALF limit
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "saturated == if primary_amps > rated_amps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "saturated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CT: 120A > 100A ALF limit → saturated");
}

#[test]
fn phase_error() {
    let mut ctx = VerificationContext::new();
    for v in &["phase_error_min", "max_phase_min"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("phase_ok", i32_ty());
    // Phase displacement: minutes of arc. Class 0.2: ±10 min
    ctx.push_obligation(ProofObligation::assume("pe", "phase_error_min == 5"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_phase_min == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "phase_ok == if phase_error_min <= max_phase_min { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "phase_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CT: 5 min phase error ≤ 10 min max → phase OK");
}

#[test]
fn voltage_output() {
    let mut ctx = VerificationContext::new();
    for v in &["secondary_ma", "burden_ohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voltage_mv", u32_ty());
    // V = I × R. Precompute: 50mA × 10Ω = 500mV
    ctx.push_obligation(ProofObligation::assume("sm", "secondary_ma == 50"));
    ctx.push_obligation(ProofObligation::assume("bo", "burden_ohms == 10"));
    ctx.push_obligation(ProofObligation::assume("vm", "voltage_mv == 500")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_500", "voltage_mv == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CT: 50mA × 10Ω = 500mV output (precomputed)");
}

#[test]
fn open_circuit_protection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_protection", u32_ty());
    ctx.declare_var_typed("safe", i32_ty());
    // Open secondary on loaded CT → dangerous voltage spike. Must have protection.
    ctx.push_obligation(ProofObligation::assume("hp", "has_protection == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "safe == if has_protection == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "safe == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CT: has_protection=1 → safe against open circuit");
}

#[test]
fn frequency_range() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "min_freq_hz", "max_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // CT rated for 50/60Hz power line, some extend to harmonics
    ctx.push_obligation(ProofObligation::assume("fh", "freq_hz == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_hz == 45"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_hz == 65"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_hz >= min_freq_hz && freq_hz <= max_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CT: 50 Hz in [45, 65] → frequency OK");
}

#[test]
fn knee_point_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["knee_voltage_v", "min_knee_v"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("knee_ok", i32_ty());
    // Knee point: secondary voltage where 10% increase needs 50% more current
    ctx.push_obligation(ProofObligation::assume("kv", "knee_voltage_v == 200"));
    ctx.push_obligation(ProofObligation::assume("mk", "min_knee_v == 150"));
    ctx.push_obligation(ProofObligation::assume(
        "ko_def",
        "knee_ok == if knee_voltage_v >= min_knee_v { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "knee_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CT: 200V knee ≥ 150V min → knee OK");
}

#[test]
fn window_size() {
    let mut ctx = VerificationContext::new();
    for v in &["conductor_mm", "window_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits", i32_ty());
    // CT window must accommodate conductor
    ctx.push_obligation(ProofObligation::assume("cm", "conductor_mm == 20"));
    ctx.push_obligation(ProofObligation::assume("wm", "window_mm == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fits == if conductor_mm < window_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CT: 20mm conductor < 30mm window → fits");
}
