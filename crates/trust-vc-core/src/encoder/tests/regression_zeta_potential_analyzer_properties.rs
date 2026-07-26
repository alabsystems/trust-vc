// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_zeta_potential_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "zp >= 0 && zp <= 500"));
    ctx.push_obligation(ProofObligation::assert("bounded", "zp >= 0 && zp <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zeta potential in [0, 500] mV should stay bounded");
}

#[test]
fn test_zeta_mobility_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mob_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "mob_x10000 >= 1 && mob_x10000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "mob_x10000 >= 1 && mob_x10000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mobility x10000 in [1, 100000] should stay bounded",
    );
}

#[test]
fn test_zeta_particle_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sz", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "sz >= 1 && sz <= 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sz >= 1 && sz <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "particle size in [1, 100000] nm should stay bounded",
    );
}

#[test]
fn test_zeta_laser_wavelength_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "wl >= 400 && wl <= 900"));
    ctx.push_obligation(ProofObligation::assert("bounded", "wl >= 400 && wl <= 900"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser wavelength in [400, 900] nm should stay bounded",
    );
}

#[test]
fn test_zeta_sample_volume_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vol_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "vol_x10 >= 5 && vol_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "vol_x10 >= 5 && vol_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample volume x10 in [5, 10000] should stay bounded",
    );
}

#[test]
fn test_zeta_electrode_spacing_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gap_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "gap_x10 >= 10 && gap_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "gap_x10 >= 10 && gap_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "electrode spacing x10 in [10, 200] should stay bounded",
    );
}

#[test]
fn test_zeta_measurement_technique_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tech", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "tech == 1 || tech == 2 || tech == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "tech == 1 || tech == 2 || tech == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement technique should be one of three values",
    );
}

#[test]
fn test_zeta_cell_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cell", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "cell == 1 || cell == 2 || cell == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "cell == 1 || cell == 2 || cell == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cell type should be one of three values");
}

#[test]
fn test_zeta_model_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("model", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "model == 1 || model == 2 || model == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "model == 1 || model == 2 || model == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "model should be one of three values");
}

#[test]
fn test_zeta_autotitration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("at", i32_ty());
    ctx.push_obligation(ProofObligation::assume("valid", "at == 0 || at == 1"));
    ctx.push_obligation(ProofObligation::assert("bounded", "at == 0 || at == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "autotitration flag should be boolean");
}
