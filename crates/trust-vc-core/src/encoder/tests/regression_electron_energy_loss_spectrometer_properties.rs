// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_eels_energy_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_ev", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_ev_val",
        "energy_ev == 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_ev_bounded",
        "energy_ev >= 1 && energy_ev <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "energy loss 2000 eV in [1, 5000]");
}

#[test]
fn test_eels_energy_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume("res_x100_val", "res_x100 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "res_x100_bounded",
        "res_x100 >= 1 && res_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "energy resolution 0.10 meV (x100=10) in [1, 10000]",
    );
}

#[test]
fn test_eels_collection_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("angle_x10_val", "angle_x10 == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "angle_x10_bounded",
        "angle_x10 >= 1 && angle_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "collection angle 20.0 mrad (x10=200) in [1, 1000]");
}

#[test]
fn test_eels_beam_energy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("beam_kv", i32_ty());
    ctx.push_obligation(ProofObligation::assume("beam_kv_val", "beam_kv == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "beam_kv_bounded",
        "beam_kv >= 20 && beam_kv <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "beam energy 200 kV in [20, 300]");
}

#[test]
fn test_eels_dispersion_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("disp_x10_val", "disp_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "disp_x10_bounded",
        "disp_x10 >= 1 && disp_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dispersion 5.0 um/eV (x10=50) in [1, 500]");
}

#[test]
fn test_eels_ccd_pixels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pixels", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pixels_val", "pixels == 2048"));
    ctx.push_obligation(ProofObligation::assert(
        "pixels_bounded",
        "pixels >= 256 && pixels <= 4096",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CCD pixels 2048 in [256, 4096]");
}

#[test]
fn test_eels_spectrometer_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spec_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("spec_type_val", "spec_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "spec_type_valid",
        "spec_type == 1 || spec_type == 2 || spec_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectrometer type 1=magnetic-prism in {1=magnetic-prism, 2=omega-filter, 3=retarding-field}");
}

#[test]
fn test_eels_acquisition_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acq_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("acq_mode_val", "acq_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "acq_mode_valid",
        "acq_mode == 1 || acq_mode == 2 || acq_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "acquisition mode 1=spectrum in {1=spectrum, 2=spectrum-imaging, 3=EFTEM}",
    );
}

#[test]
fn test_eels_edge_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("edge_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("edge_type_val", "edge_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "edge_type_valid",
        "edge_type == 1 || edge_type == 2 || edge_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "edge type 1=core-loss in {1=core-loss, 2=low-loss, 3=zero-loss}",
    );
}

#[test]
fn test_eels_auto_drift_correction_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "auto_drift_correction_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic drift correction flag=1 yields active (1)",
    );
}
