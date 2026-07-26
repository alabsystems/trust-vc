// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Dispersion voltage (DV) must be within 500–5000 V for stable ion separation.
#[test]
fn test_faims_ms_dispersion_voltage_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dv_a",
        "voltage >= 500 && voltage <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dv_c",
        "voltage >= 500 && voltage <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAIMS MS dispersion voltage bounded 500-5000 V");
}

/// Compensation voltage (CV) scaled by 100 must be within 1–10000 (0.01–100 V actual).
#[test]
fn test_faims_ms_compensation_voltage_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cv_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cv_a",
        "cv_x100 >= 1 && cv_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cv_c",
        "cv_x100 >= 1 && cv_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FAIMS MS compensation voltage x100 bounded 1-10000",
    );
}

/// Carrier gas flow rate scaled by 10 must be within 1–200 (0.1–20.0 L/min actual).
#[test]
fn test_faims_ms_carrier_gas_flow_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cf_a",
        "flow_x10 >= 1 && flow_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cf_c",
        "flow_x10 >= 1 && flow_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAIMS MS carrier gas flow x10 bounded 1-200");
}

/// Electrode gap scaled by 100 must be within 10–500 (0.10–5.00 mm actual).
#[test]
fn test_faims_ms_electrode_gap_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gap_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eg_a",
        "gap_x100 >= 10 && gap_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eg_c",
        "gap_x100 >= 10 && gap_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAIMS MS electrode gap x100 bounded 10-500");
}

/// Ion source temperature with +100 offset must be within 100–500 (0–400 C actual).
#[test]
fn test_faims_ms_source_temperature_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "temp_off >= 100 && temp_off <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "temp_off >= 100 && temp_off <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FAIMS MS source temperature offset bounded 100-500",
    );
}

/// Waveform frequency must be within 100–10000 kHz for effective ion oscillation.
#[test]
fn test_faims_ms_waveform_frequency_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frequency", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wf_a",
        "frequency >= 100 && frequency <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wf_c",
        "frequency >= 100 && frequency <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAIMS MS waveform frequency bounded 100-10000 kHz");
}

/// Electrode geometry must be one of: 1=planar, 2=cylindrical, 3=dome.
#[test]
fn test_faims_ms_electrode_geometry_enum() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geometry", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ge_a",
        "geometry == 1 || geometry == 2 || geometry == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ge_c",
        "geometry == 1 || geometry == 2 || geometry == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FAIMS MS electrode geometry is planar, cylindrical, or dome",
    );
}

/// Carrier gas must be one of: 1=nitrogen, 2=helium, 3=air.
#[test]
fn test_faims_ms_carrier_gas_enum() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("carrier", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cg_a",
        "carrier == 1 || carrier == 2 || carrier == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cg_c",
        "carrier == 1 || carrier == 2 || carrier == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAIMS MS carrier gas is nitrogen, helium, or air");
}

/// Waveform shape must be one of: 1=bisinusoidal, 2=rectangular, 3=clipped-sinusoidal.
#[test]
fn test_faims_ms_waveform_shape_enum() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("waveform", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ws_a",
        "waveform == 1 || waveform == 2 || waveform == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ws_c",
        "waveform == 1 || waveform == 2 || waveform == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FAIMS MS waveform shape is bisinusoidal, rectangular, or clipped-sinusoidal",
    );
}

/// Automatic compensation scan flag must be boolean (0 or 1).
#[test]
fn test_faims_ms_auto_compensation_scan_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ac_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("ac_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAIMS MS auto compensation scan flag is boolean");
}
