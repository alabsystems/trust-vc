// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_faims_dispersion_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_v", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dv_a",
        "disp_v >= 500 && disp_v <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dv_c",
        "disp_v >= 500 && disp_v <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dispersion voltage in [500, 6000] V");
}

#[test]
fn test_faims_compensation_voltage_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cv_off100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cv_a",
        "cv_off100 >= 0 && cv_off100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cv_c",
        "cv_off100 >= 0 && cv_off100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compensation voltage +100 offset x100 in [0, 10000] representing -100 to 0 V",
    );
}

#[test]
fn test_faims_carrier_gas_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gf_a",
        "gas_x10 >= 5 && gas_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gf_c",
        "gas_x10 >= 5 && gas_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "carrier gas flow x10 in [5, 100] representing 0.5-10.0 L/min",
    );
}

#[test]
fn test_faims_electrode_gap_um_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gap_um", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eg_a",
        "gap_um >= 100 && gap_um <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eg_c",
        "gap_um >= 100 && gap_um <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "electrode gap in [100, 5000] um");
}

#[test]
fn test_faims_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("faims_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ft_a",
        "faims_temp >= 20 && faims_temp <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ft_c",
        "faims_temp >= 20 && faims_temp <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FAIMS temperature in [20, 200] C");
}

#[test]
fn test_faims_waveform_frequency_khz_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_khz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wf_a",
        "freq_khz >= 100 && freq_khz <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wf_c",
        "freq_khz >= 100 && freq_khz <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "waveform frequency in [100, 5000] kHz");
}

#[test]
fn test_faims_electrode_geometry_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geom", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eg_a2",
        "geom == 1 || geom == 2 || geom == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eg_c2",
        "geom == 1 || geom == 2 || geom == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "electrode geometry: planar, cylindrical, or dome");
}

#[test]
fn test_faims_waveform_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("waveform", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wv_a",
        "waveform == 1 || waveform == 2 || waveform == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wv_c",
        "waveform == 1 || waveform == 2 || waveform == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "waveform: bisinusoidal, rectangular, or clipped sinusoidal",
    );
}

#[test]
fn test_faims_carrier_gas_classification() {
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
    expect_verified(
        &result,
        "carrier gas: nitrogen, helium-nitrogen mix, or carbon dioxide",
    );
}

#[test]
fn test_faims_inner_electrode_rotation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotation", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ro_a",
        "rotation == 0 || rotation == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ro_c",
        "rotation == 0 || rotation == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inner electrode rotation flag is boolean");
}
