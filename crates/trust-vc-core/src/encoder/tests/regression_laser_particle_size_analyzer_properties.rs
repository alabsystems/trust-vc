// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_measurement_range_min_scaled() {
    // Measurement range minimum in units of 0.01 nm (×100 nm scaling)
    // Value of 1 = 0.01 nm, must be positive and within instrument capability
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_min_x100", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rm", "range_min_x100 == 50")); // 0.50 nm
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if range_min_x100 >= 1 && range_min_x100 <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "range min 0.50nm (50 x0.01nm) in [0.01nm, 100nm]");
}

#[test]
fn test_measurement_range_max_bounded() {
    // Maximum measurable particle size in micrometers, bounded 1000-10000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_max_um", u32_ty());
    ctx.declare_var_typed("in_bounds", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rm", "range_max_um == 3500")); // 3500 um
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "in_bounds == if range_max_um >= 1000 && range_max_um <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_bounds == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "range max 3500um within [1000, 10000]");
}

#[test]
fn test_laser_wavelength_bounded() {
    // Laser wavelength in nm, typically 400-900 nm (visible to near-IR)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wl", "wavelength_nm == 632")); // He-Ne laser
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if wavelength_nm >= 400 && wavelength_nm <= 900 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength 632nm within [400, 900]");
}

#[test]
fn test_detector_count_bounded() {
    // Number of photodetectors, bounded 16-128
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detectors", u32_ty());
    ctx.declare_var_typed("sufficient", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "detectors == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "sufficient == if detectors >= 16 && detectors <= 128 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "sufficient == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "64 detectors within [16, 128]");
}

#[test]
fn test_accuracy_scaled() {
    // Accuracy in units of 0.1% (×10 scaling), e.g. 10 = 1.0%
    // Must be positive and within realistic bounds (1-50 = 0.1%-5.0%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "accuracy_x10 == 10")); // 1.0%
    ctx.push_obligation(ProofObligation::assume(
        "ac_def",
        "acceptable == if accuracy_x10 >= 1 && accuracy_x10 <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 1.0% (10 x0.1%) within [0.1%, 5.0%]");
}

#[test]
fn test_dispersal_method_disjunction() {
    // Dispersal method: 1=wet, 2=dry, 3=spray
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dispersal", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dm", "dispersal == 2")); // dry dispersal
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if dispersal == 1 || dispersal == 2 || dispersal == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dry dispersal (2) is valid {1=wet,2=dry,3=spray}");
}

#[test]
fn test_optical_model_disjunction() {
    // Optical model: 1=Mie, 2=Fraunhofer, 3=modified Mie
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("model", i32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m", "model == 1")); // Mie scattering
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if model == 1 || model == 2 || model == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Mie model (1) is valid {1=Mie,2=Fraunhofer,3=modMie}",
    );
}

#[test]
fn test_measurement_time_bounded() {
    // Measurement time in seconds, bounded 5-120
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_time_s", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mt", "meas_time_s == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if meas_time_s >= 5 && meas_time_s <= 120 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement time 30s within [5, 120]");
}

#[test]
fn test_repeatability_scaled() {
    // Repeatability in units of 0.01% (×100 scaling), e.g. 50 = 0.50%
    // Must be positive and within realistic bounds (1-500 = 0.01%-5.00%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("repeat_x100", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "repeat_x100 == 50")); // 0.50%
    ctx.push_obligation(ProofObligation::assume(
        "ac_def",
        "acceptable == if repeat_x100 >= 1 && repeat_x100 <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "repeatability 0.50% (50 x0.01%) within [0.01%, 5.00%]",
    );
}

#[test]
fn test_auto_alignment_boolean_flag() {
    // Auto-alignment feature: boolean flag encoded as i32 (1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_align_flag", i32_ty());
    ctx.declare_var_typed("auto_align", i32_ty());
    ctx.push_obligation(ProofObligation::assume("af", "auto_align_flag == 1")); // enabled
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "auto_align == if auto_align_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("enabled", "auto_align == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-alignment enabled (flag=1)");
}
