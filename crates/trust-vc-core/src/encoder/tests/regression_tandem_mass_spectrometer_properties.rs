// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_tandem_ms_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_bounds",
        "mass >= 10 && mass <= 200000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mass_in_range",
        "mass >= 10 && mass <= 200000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range bounded 10..200000 amu");
}

#[test]
fn test_tandem_ms_collision_energy_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_bounds",
        "energy_x10 >= 1 && energy_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_in_range",
        "energy_x10 >= 1 && energy_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "collision energy x10 bounded 1..2000 representing 0.1 eV units",
    );
}

#[test]
fn test_tandem_ms_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolving", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_bounds",
        "resolving >= 1000 && resolving <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_in_range",
        "resolving >= 1000 && resolving <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolving power bounded 1000..1000000");
}

#[test]
fn test_tandem_ms_scan_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_bounds",
        "speed >= 100 && speed <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_in_range",
        "speed >= 100 && speed <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan speed bounded 100..100000 amu/sec");
}

#[test]
fn test_tandem_ms_sensitivity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sens_bounds",
        "sens_x100 >= 1 && sens_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sens_in_range",
        "sens_x100 >= 1 && sens_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sensitivity x100 bounded 1..100000 representing 0.01 counts/fg",
    );
}

#[test]
fn test_tandem_ms_ion_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("src", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "src_valid",
        "src == 1 || src == 2 || src == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "src_in_set",
        "src == 1 || src == 2 || src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ion source three-way 1=ESI 2=APCI 3=MALDI");
}

#[test]
fn test_tandem_ms_analyzer_geometry_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ag_valid",
        "ag == 1 || ag == 2 || ag == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ag_in_set",
        "ag == 1 || ag == 2 || ag == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analyzer geometry three-way 1=triple-quadrupole 2=Q-TOF 3=ion-trap",
    );
}

#[test]
fn test_tandem_ms_fragmentation_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fm_valid",
        "fm == 1 || fm == 2 || fm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fm_in_set",
        "fm == 1 || fm == 2 || fm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fragmentation mode three-way 1=CID 2=HCD 3=ETD");
}

#[test]
fn test_tandem_ms_auto_ms2_trigger_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_bool",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto MS2 trigger flag boolean 0 or 1");
}

#[test]
fn test_tandem_ms_precursor_isolation_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("iso_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "iso_bounds",
        "iso_x10 >= 1 && iso_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "iso_in_range",
        "iso_x10 >= 1 && iso_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precursor isolation window x10 bounded 1..100 representing 0.1 Da width",
    );
}
