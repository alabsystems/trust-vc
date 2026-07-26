// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn interpolation_factor() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("factor", u32_ty());
    ctx.declare_var_typed("valid_factor", i32_ty());
    // Interpolation factors: power of 2 (1, 2, 4, 8, 16, 32, 64, 128)
    ctx.push_obligation(ProofObligation::assume("f", "factor == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_factor == if factor == 1 || factor == 2 || factor == 4 || factor == 8 || factor == 16 || factor == 32 || factor == 64 || factor == 128 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_factor == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical interp: 32× is a valid interpolation factor",
    );
}

#[test]
fn effective_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["base_cpr", "interp_factor"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("effective_cpr", u32_ty());
    // Effective CPR = base × interpolation × 4 (quadrature). Precompute: 1024 × 32 × 4 = 131072
    ctx.push_obligation(ProofObligation::assume("bc", "base_cpr == 1024"));
    ctx.push_obligation(ProofObligation::assume("if_", "interp_factor == 32"));
    ctx.push_obligation(ProofObligation::assume("ec", "effective_cpr == 131072")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_131072",
        "effective_cpr == 131072",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical interp: 1024 × 32 × 4 = 131072 CPR (precomputed)",
    );
}

#[test]
fn signal_amplitude() {
    let mut ctx = VerificationContext::new();
    for v in &["amplitude_mv", "min_amplitude_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("signal_ok", i32_ty());
    // Analog signal amplitude must be sufficient for interpolation
    ctx.push_obligation(ProofObligation::assume("am", "amplitude_mv == 800"));
    ctx.push_obligation(ProofObligation::assume("ma", "min_amplitude_mv == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "signal_ok == if amplitude_mv >= min_amplitude_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "signal_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical interp: 800mV amplitude ≥ 200mV min → OK");
}

#[test]
fn lissajous_radius() {
    let mut ctx = VerificationContext::new();
    for v in &["radius", "min_radius", "max_radius"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("radius_ok", i32_ty());
    // Lissajous circle radius (sin/cos signal quality indicator)
    ctx.push_obligation(ProofObligation::assume("r", "radius == 450"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_radius == 300"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_radius == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "radius_ok == if radius >= min_radius && radius <= max_radius { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "radius_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical interp: Lissajous radius 450 in [300, 600] → OK",
    );
}

#[test]
fn offset_error() {
    let mut ctx = VerificationContext::new();
    for v in &["offset_mv", "max_offset_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("offset_ok", i32_ty());
    // DC offset error in analog signals
    ctx.push_obligation(ProofObligation::assume("om", "offset_mv == 15"));
    ctx.push_obligation(ProofObligation::assume("mo", "max_offset_mv == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "offset_ok == if offset_mv <= max_offset_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "offset_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical interp: 15mV offset ≤ 50mV max → OK");
}

#[test]
fn phase_error() {
    let mut ctx = VerificationContext::new();
    for v in &["phase_err_x10", "max_phase_err_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("phase_ok", i32_ty());
    // Phase quadrature error (ideal = 90°, ×10 for 0.1° resolution)
    ctx.push_obligation(ProofObligation::assume("pe", "phase_err_x10 == 5")); // 0.5°
    ctx.push_obligation(ProofObligation::assume("mp", "max_phase_err_x10 == 20")); // 2.0°
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "phase_ok == if phase_err_x10 <= max_phase_err_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "phase_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical interp: 0.5° phase error ≤ 2.0° max → OK");
}

#[test]
fn adc_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_bits", "min_adc_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("adc_ok", i32_ty());
    // ADC for sin/cos interpolation (12-16 bit typical)
    ctx.push_obligation(ProofObligation::assume("ab", "adc_bits == 14"));
    ctx.push_obligation(ProofObligation::assume("ma", "min_adc_bits == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "adc_ok == if adc_bits >= min_adc_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "adc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical interp: 14-bit ADC ≥ 12-bit min → OK");
}

#[test]
fn max_velocity() {
    let mut ctx = VerificationContext::new();
    for v in &["rpm", "max_rpm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vel_ok", i32_ty());
    // Maximum shaft speed for reliable interpolation
    ctx.push_obligation(ProofObligation::assume("r", "rpm == 6000"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_rpm == 12000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vel_ok == if rpm <= max_rpm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vel_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical interp: 6000 RPM ≤ 12000 max → OK");
}

#[test]
fn sub_divisional_error() {
    let mut ctx = VerificationContext::new();
    for v in &["sde_arcsec", "max_sde_arcsec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sde_ok", i32_ty());
    // Sub-divisional error (SDE): interpolation accuracy
    ctx.push_obligation(ProofObligation::assume("sa", "sde_arcsec == 3"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_sde_arcsec == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sde_ok == if sde_arcsec <= max_sde_arcsec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sde_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optical interp: 3 arcsec SDE ≤ 10 max → OK");
}

#[test]
fn reference_mark() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_ref", u32_ty());
    ctx.declare_var_typed("absolute_home", i32_ty());
    // Reference mark: provides absolute position (one per revolution)
    ctx.push_obligation(ProofObligation::assume("hr", "has_ref == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ah_def",
        "absolute_home == if has_ref == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "absolute_home == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Optical interp: has_ref=1 → absolute home available",
    );
}
