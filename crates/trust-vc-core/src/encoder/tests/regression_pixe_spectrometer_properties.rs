// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Proton energy ×10 bounded (range 10-50 representing 1.0-5.0 MeV).
#[test]
fn proton_energy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_range",
        "energy_x10 >= 10 && energy_x10 <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_positive",
        "energy_x10 >= 10 && energy_x10 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "proton energy x10 in [10,50] representing 1.0-5.0 MeV",
    );
}

/// Beam current ×10 bounded (range 1-1000 representing 0.1-100.0 nA).
#[test]
fn beam_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "current_x10 >= 1 && current_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "current_positive",
        "current_x10 >= 1 && current_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beam current x10 in [1,1000] representing 0.1-100.0 nA",
    );
}

/// Beam spot size ×10 bounded (range 1-1000 representing 0.1-100.0 um).
#[test]
fn beam_spot_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spot_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spot_range",
        "spot_x10 >= 1 && spot_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spot_positive",
        "spot_x10 >= 1 && spot_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beam spot size x10 in [1,1000] representing 0.1-100.0 um",
    );
}

/// Detection limit ×100 bounded (range 1-10000 representing 0.01-100.00 ppm).
#[test]
fn detection_limit_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("limit_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "limit_range",
        "limit_x100 >= 1 && limit_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "limit_positive",
        "limit_x100 >= 1 && limit_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection limit x100 in [1,10000] representing 0.01-100.00 ppm",
    );
}

/// Energy resolution bounded (100-300 eV).
#[test]
fn energy_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_ev", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_range",
        "resolution_ev >= 100 && resolution_ev <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_valid",
        "resolution_ev >= 100 && resolution_ev <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "energy resolution in [100,300] eV");
}

/// Number of detectable elements bounded (1-80).
#[test]
fn detectable_elements_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_elements", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "elements_range",
        "num_elements >= 1 && num_elements <= 80",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "elements_valid",
        "num_elements >= 1 && num_elements <= 80",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detectable elements in [1,80] (H through Hg)");
}

/// Ion source 3-way disjunction (1=duoplasmatron, 2=RF, 3=Penning).
#[test]
fn ion_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ion_source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ion_source_valid",
        "ion_source == 1 || ion_source == 2 || ion_source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ion_source_bounded",
        "ion_source >= 1 && ion_source <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ion source is duoplasmatron(1), RF(2), or Penning(3)",
    );
}

/// Detector type 3-way disjunction (1=SDD, 2=Si-Li, 3=HPGe).
#[test]
fn detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detector_valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detector_bounded",
        "detector >= 1 && detector <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector is SDD(1), Si-Li(2), or HPGe(3)");
}

/// Analysis mode 3-way disjunction (1=bulk, 2=micro-probe, 3=external-beam).
#[test]
fn analysis_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_bounded",
        "mode >= 1 && mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analysis mode is bulk(1), micro-probe(2), or external-beam(3)",
    );
}

/// Automatic beam steering boolean flag (== 0 || == 1).
#[test]
fn beam_steering_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_steer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "steer_flag",
        "auto_steer == 0 || auto_steer == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "steer_bounded",
        "auto_steer >= 0 && auto_steer <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "beam steering flag is boolean (0 or 1)");
}
