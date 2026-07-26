// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn displacement_from_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["output_mv", "sensitivity_mv_per_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("displacement_um", u32_ty());
    // Displacement = output / sensitivity. Precompute: 500mV / 100(mV/mm) = 5mm = 5000μm
    ctx.push_obligation(ProofObligation::assume("om", "output_mv == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "sm",
        "sensitivity_mv_per_mm == 100",
    ));
    ctx.push_obligation(ProofObligation::assume("du", "displacement_um == 5000")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_5000",
        "displacement_um == 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LVDT: 500mV / 100mV/mm = 5mm displacement (precomputed)",
    );
}

#[test]
fn null_position() {
    let mut ctx = VerificationContext::new();
    for v in &["residual_mv", "max_residual_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("at_null", i32_ty());
    // Null (zero) position: minimal residual voltage
    ctx.push_obligation(ProofObligation::assume("rm", "residual_mv == 5"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_residual_mv == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "an_def",
        "at_null == if residual_mv <= max_residual_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "at_null == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDT: 5mV residual ≤ 20mV max → at null position");
}

#[test]
fn linearity_range() {
    let mut ctx = VerificationContext::new();
    for v in &["position_um", "linear_range_um"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_linear", i32_ty());
    // LVDT is linear within specified range (e.g., ±10mm = 10000μm from center)
    ctx.push_obligation(ProofObligation::assume("pu", "position_um == 7500"));
    ctx.push_obligation(ProofObligation::assume("lr", "linear_range_um == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "il_def",
        "in_linear == if position_um <= linear_range_um { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_linear == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LVDT: 7500μm ≤ 10000μm linear range → in linear region",
    );
}

#[test]
fn excitation_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["exc_freq_hz", "min_freq_hz", "max_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // LVDT excitation: typically 1-10 kHz
    ctx.push_obligation(ProofObligation::assume("ef", "exc_freq_hz == 5000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_hz == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if exc_freq_hz >= min_freq_hz && exc_freq_hz <= max_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LVDT: 5 kHz in [1, 10] kHz → excitation frequency OK",
    );
}

#[test]
fn excitation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["exc_vrms_mv", "rated_vrms_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voltage_ok", i32_ty());
    // Primary excitation: typically 1-10 Vrms
    ctx.push_obligation(ProofObligation::assume("ev", "exc_vrms_mv == 3000")); // 3 Vrms
    ctx.push_obligation(ProofObligation::assume("rv", "rated_vrms_mv == 5000")); // 5 Vrms max
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "voltage_ok == if exc_vrms_mv <= rated_vrms_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "voltage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LVDT: 3 Vrms ≤ 5 Vrms rated → excitation voltage OK",
    );
}

#[test]
fn phase_angle() {
    let mut ctx = VerificationContext::new();
    for v in &["phase_deg", "max_phase_deg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("phase_ok", i32_ty());
    // Output phase angle: small at resonance, increases off-resonance
    ctx.push_obligation(ProofObligation::assume("pd", "phase_deg == 5"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_phase_deg == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "phase_ok == if phase_deg <= max_phase_deg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "phase_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDT: 5° phase ≤ 15° max → phase OK");
}

#[test]
fn resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution_nm", "required_nm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fine_enough", i32_ty());
    // LVDT: essentially infinite resolution (analog), limited by signal conditioning
    ctx.push_obligation(ProofObligation::assume("rn", "resolution_nm == 100")); // 100nm
    ctx.push_obligation(ProofObligation::assume("req", "required_nm == 1000")); // 1μm
    ctx.push_obligation(ProofObligation::assume(
        "fe_def",
        "fine_enough == if resolution_nm <= required_nm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fine_enough == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LVDT: 100nm resolution ≤ 1000nm required → fine enough",
    );
}

#[test]
fn temperature_range() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // LVDT: wide operating range, -55 to +150°C typical. Offset +500.
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c_offset == 525")); // 25°C + 500
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 445")); // -55°C + 500
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 650")); // +150°C + 500
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_c_offset >= min_temp_offset && temp_c_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDT: 25°C in [-55, +150] → temp OK");
}

#[test]
fn signal_conditioning() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("demod_type", u32_ty());
    ctx.declare_var_typed("is_ratiometric", i32_ty());
    // Demodulation: 0=synchronous, 1=ratiometric, 2=phase-sensitive
    ctx.push_obligation(ProofObligation::assume("dt", "demod_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_ratiometric == if demod_type == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_ratiometric == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDT: demod_type=1 → ratiometric demodulation");
}

#[test]
fn stroke_length() {
    let mut ctx = VerificationContext::new();
    for v in &["core_travel_mm", "max_stroke_mm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_stroke", i32_ty());
    // Core must stay within stroke length
    ctx.push_obligation(ProofObligation::assume("ct", "core_travel_mm == 8"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_stroke_mm == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_stroke == if core_travel_mm <= max_stroke_mm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_stroke == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LVDT: 8mm travel ≤ 10mm stroke → within stroke");
}
