// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Field Flow Fractionation (FFF) spectrometer property verification.
// Parameters are encoded as integers with scaling factors where fractional
// precision is needed (e.g., cross-flow rate in units of 0.01 mL/min).

#[test]
fn test_fff_channel_length_cm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channel_len", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channel_len >= 10 && channel_len <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("nominal", "channel_len == 45"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "channel_len >= 10 && channel_len <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channel length 45 cm is within [10, 100] cm");
}

#[test]
fn test_fff_channel_thickness_x10um_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thickness", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "thickness >= 100 && thickness <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("nominal", "thickness == 2500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "thickness >= 100 && thickness <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "channel thickness 2500 (250.0 um) is within [100, 5000]",
    );
}

#[test]
fn test_fff_cross_flow_rate_x100_ml_per_min_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cross_flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "cross_flow >= 1 && cross_flow <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("nominal", "cross_flow == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "cross_flow >= 1 && cross_flow <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cross-flow rate 100 (1.00 mL/min) is within [1, 1000]",
    );
}

#[test]
fn test_fff_size_range_nm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("size_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "size_range >= 1 && size_range <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("nominal", "size_range == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "size_range >= 1 && size_range <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "particle size range 10000 nm is within [1, 100000] nm",
    );
}

#[test]
fn test_fff_detector_wavelength_nm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "wavelength >= 200 && wavelength <= 800",
    ));
    ctx.push_obligation(ProofObligation::assume("nominal", "wavelength == 658"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "wavelength >= 200 && wavelength <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector wavelength 658 nm is within [200, 800] nm",
    );
}

#[test]
fn test_fff_sample_volume_x10ul_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_vol", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sample_vol >= 1 && sample_vol <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("nominal", "sample_vol == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sample_vol >= 1 && sample_vol <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample volume 100 (10.0 uL) is within [1, 5000]");
}

#[test]
fn test_fff_separation_field_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sep_field", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sep_field >= 1 && sep_field <= 3",
    ));
    ctx.push_obligation(ProofObligation::assume("nominal", "sep_field == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "sep_field == 1 || sep_field == 2 || sep_field == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "separation field 1 (flow) is one of {1=flow, 2=thermal, 3=sedimentation}",
    );
}

#[test]
fn test_fff_detector_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "det_type >= 1 && det_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assume("nominal", "det_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "det_type == 1 || det_type == 2 || det_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type 2 (MALS) is one of {1=UV-Vis, 2=MALS, 3=DLS}",
    );
}

#[test]
fn test_fff_membrane_material_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("membrane", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "membrane >= 1 && membrane <= 3",
    ));
    ctx.push_obligation(ProofObligation::assume("nominal", "membrane == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "membrane == 1 || membrane == 2 || membrane == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "membrane material 1 (regenerated-cellulose) is one of {1=RC, 2=PES, 3=PVDF}",
    );
}

#[test]
fn test_fff_auto_focus_relax_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("enabled", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "focus_active",
        "(if flag == 1 { 1 } else { 0 }) == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto focus/relax flag enabled implies active");
}
