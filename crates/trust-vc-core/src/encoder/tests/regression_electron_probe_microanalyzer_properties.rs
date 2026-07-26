// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_accelerating_voltage_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_kv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage_kv >= 1 && voltage_kv <= 30",
    ));
    ctx.push_obligation(ProofObligation::assume("voltage_val", "voltage_kv == 15"));
    ctx.push_obligation(ProofObligation::assert(
        "within_bounds",
        "voltage_kv >= 1 && voltage_kv <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accelerating voltage 15 kV within [1, 30] range");
}

#[test]
fn test_beam_current_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_na", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "current_na >= 1 && current_na <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("current_val", "current_na == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "within_bounds",
        "current_na >= 1 && current_na <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "beam current 20 nA within [1, 1000] range");
}

#[test]
fn test_spatial_resolution_scaled() {
    // Spatial resolution in units of 0.1 nm (x10 scaling)
    // 10 = 1.0 nm, 10000 = 1000.0 nm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_range",
        "resolution_x10 >= 10 && resolution_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "resolution_val",
        "resolution_x10 == 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "within_bounds",
        "resolution_x10 >= 10 && resolution_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spatial resolution 50.0 nm (x10=500) within [1.0, 1000.0] nm",
    );
}

#[test]
fn test_detectable_elements_atomic_number() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atomic_num", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "element_range",
        "atomic_num >= 4 && atomic_num <= 92",
    ));
    ctx.push_obligation(ProofObligation::assume("element_val", "atomic_num == 26"));
    ctx.push_obligation(ProofObligation::assert(
        "within_bounds",
        "atomic_num >= 4 && atomic_num <= 92",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "iron (Z=26) detectable within [4, 92] range");
}

#[test]
fn test_number_of_spectrometers_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spec_range",
        "num_spec >= 1 && num_spec <= 5",
    ));
    ctx.push_obligation(ProofObligation::assume("spec_val", "num_spec == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "within_bounds",
        "num_spec >= 1 && num_spec <= 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "4 spectrometers within [1, 5] bound");
}

#[test]
fn test_xray_detector_type_disjunction() {
    // 1=WDS, 2=EDS, 3=combined
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_detector",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("detector_val", "detector == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "is_valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "WDS detector (1) is valid in {1=WDS, 2=EDS, 3=combined}",
    );
}

#[test]
fn test_electron_source_disjunction() {
    // 1=tungsten, 2=LaB6, 3=field-emission
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_source",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("source_val", "source == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "is_valid",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "field-emission source (3) is valid in {1=W, 2=LaB6, 3=FE}",
    );
}

#[test]
fn test_analysis_mode_disjunction() {
    // 1=spot, 2=line-scan, 3=area-map
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_mode",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "is_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "line-scan mode (2) is valid in {1=spot, 2=line, 3=area}",
    );
}

#[test]
fn test_detection_limit_scaled() {
    // Detection limit in units of 0.01 ppm (x100 scaling)
    // 1 = 0.01 ppm, 10000 = 100.00 ppm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("limit_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "limit_range",
        "limit_x100 >= 1 && limit_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("limit_val", "limit_x100 == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "within_bounds",
        "limit_x100 >= 1 && limit_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection limit 1.00 ppm (x100=100) within [0.01, 100.00] ppm",
    );
}

#[test]
fn test_cathodoluminescence_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cl_enabled", i32_ty());
    ctx.declare_var_typed("cl_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "cl_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "active_def",
        "cl_active == if cl_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_active", "cl_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cathodoluminescence enabled flag propagates to active",
    );
}
