// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pt100_resistance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_c_offset", u32_ty());
    ctx.declare_var_typed("resistance_x10", u32_ty());
    // PT100: 100Ω at 0°C, α≈0.385Ω/°C. At 25°C: 109.73Ω. Use offset +500.
    // Precompute: 25°C → 1097 (×10 scale)
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c_offset == 525")); // 25°C + 500
    ctx.push_obligation(ProofObligation::assume("rx", "resistance_x10 == 1097")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1097", "resistance_x10 == 1097"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTD: PT100 at 25°C = 109.7Ω (precomputed)");
}

#[test]
fn wire_compensation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wire_config", u32_ty());
    ctx.declare_var_typed("is_4wire", i32_ty());
    // Wire configurations: 2=2-wire, 3=3-wire, 4=4-wire (best accuracy)
    ctx.push_obligation(ProofObligation::assume("wc", "wire_config == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "i4_def",
        "is_4wire == if wire_config == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_4wire == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTD: wire_config=4 → 4-wire (best accuracy)");
}

#[test]
fn excitation_current() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ua", "max_current_ua"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("current_ok", i32_ty());
    // Low excitation current minimizes self-heating (typically 100-1000μA)
    ctx.push_obligation(ProofObligation::assume("cu", "current_ua == 500"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_ua == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "current_ok == if current_ua <= max_current_ua { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTD: 500μA excitation ≤ 1000μA max → current OK");
}

#[test]
fn self_heating_error() {
    let mut ctx = VerificationContext::new();
    for v in &["self_heat_mc", "max_error_mc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("heat_ok", i32_ty());
    // Self-heating: I²R causes temperature rise. In milli-°C.
    ctx.push_obligation(ProofObligation::assume("sh", "self_heat_mc == 25")); // 0.025°C
    ctx.push_obligation(ProofObligation::assume("me", "max_error_mc == 50")); // 0.05°C
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "heat_ok == if self_heat_mc <= max_error_mc { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "heat_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTD: 25m°C self-heat ≤ 50m°C max → heat OK");
}

#[test]
fn accuracy_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("class", u32_ty());
    ctx.declare_var_typed("is_class_a", i32_ty());
    // IEC 60751: Class AA(0), A(1), B(2), C(3)
    ctx.push_obligation(ProofObligation::assume("c", "class == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "is_class_a == if class == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_class_a == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTD: class=1 → IEC Class A");
}

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c_offset", "min_offset", "max_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // PT100: -200 to +850°C. Offset +500: 300 to 1350
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c_offset == 600")); // 100°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_offset == 300")); // -200°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_offset == 1350")); // +850°C
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_c_offset >= min_offset && temp_c_offset <= max_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTD: 100°C in [-200, +850] → in range");
}

#[test]
fn adc_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_bits", "min_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resolution_ok", i32_ty());
    // RTD ADCs typically 15-24 bits for precision
    ctx.push_obligation(ProofObligation::assume("ab", "adc_bits == 24"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bits == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resolution_ok == if adc_bits >= min_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resolution_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTD: 24-bit ADC ≥ 15-bit min → resolution OK");
}

#[test]
fn filter_setting() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rejection_hz", u32_ty());
    ctx.declare_var_typed("is_50hz", i32_ty());
    // Mains rejection filter: 50Hz (EU) or 60Hz (US)
    ctx.push_obligation(ProofObligation::assume("rh", "rejection_hz == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "i5_def",
        "is_50hz == if rejection_hz == 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_50hz == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTD: rejection=50Hz → 50Hz mains filter");
}

#[test]
fn reference_resistor() {
    let mut ctx = VerificationContext::new();
    for v in &["ref_ohms", "min_ref_ohms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ref_ok", i32_ty());
    // Reference resistor: typically 400Ω for PT100 (4× RTD nominal)
    ctx.push_obligation(ProofObligation::assume("ro", "ref_ohms == 400"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_ref_ohms == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ref_ok == if ref_ohms >= min_ref_ohms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ref_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RTD: 400Ω reference ≥ 400Ω min → reference OK");
}

#[test]
fn callendar_van_dusen() {
    let mut ctx = VerificationContext::new();
    for v in &["measured_ohms_x100", "expected_ohms_x100", "tolerance_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cvd_ok", i32_ty());
    // Callendar-Van Dusen equation result. At 100°C: 138.51Ω. Precomputed.
    ctx.push_obligation(ProofObligation::assume("mo", "measured_ohms_x100 == 13845")); // 138.45Ω
    ctx.push_obligation(ProofObligation::assume("eo", "expected_ohms_x100 == 13851")); // 138.51Ω
    ctx.push_obligation(ProofObligation::assume("tx", "tolerance_x100 == 20")); // 0.20Ω
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cvd_ok == if expected_ohms_x100 - measured_ohms_x100 <= tolerance_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cvd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "RTD: |138.51-138.45| = 0.06Ω ≤ 0.20Ω tolerance → CVD OK",
    );
}
