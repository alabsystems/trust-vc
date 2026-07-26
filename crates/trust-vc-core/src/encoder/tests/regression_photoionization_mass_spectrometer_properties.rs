// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn mass_range_amu() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_range",
        "mass >= 1 && mass <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mass_range",
        "mass >= 1 && mass <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range 1-2000 amu for photoionization MS");
}

#[test]
fn photon_energy_x100_ev() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "energy_range",
        "energy_x100 >= 500 && energy_x100 <= 2500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "energy_range",
        "energy_x100 >= 500 && energy_x100 <= 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "photon energy 5.00-25.00 eV scaled by x100");
}

#[test]
fn lamp_current_x10_ma() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lamp_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lamp_range",
        "lamp_x10 >= 1 && lamp_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lamp_range",
        "lamp_x10 >= 1 && lamp_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lamp current 0.1-50.0 mA scaled by x10");
}

#[test]
fn chamber_pressure_x10000_torr() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "press_x10000 >= 1 && press_x10000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_range",
        "press_x10000 >= 1 && press_x10000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "chamber pressure 0.0001-1.0000 torr scaled by x10000",
    );
}

#[test]
fn source_temperature_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 80 && temp_off <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_range",
        "temp_off >= 80 && temp_off <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "source temperature -20 to 400 C with +100 offset");
}

#[test]
fn detection_limit_x1000_ppb() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detect_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detect_range",
        "detect_x1000 >= 1 && detect_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detect_range",
        "detect_x1000 >= 1 && detect_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection limit 0.001-10.000 ppb scaled by x1000");
}

#[test]
fn light_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "source_kind",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "source_kind",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "light source is UV-lamp, synchrotron, or laser");
}

#[test]
fn analyzer_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "analyzer_kind",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "analyzer_kind",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "analyzer is TOF, quadrupole, or magnetic-sector");
}

#[test]
fn sample_introduction_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("intro", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "intro_kind",
        "intro == 1 || intro == 2 || intro == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "intro_kind",
        "intro == 1 || intro == 2 || intro == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample introduction is GC, direct-inject, or membrane",
    );
}

#[test]
fn auto_lamp_intensity_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_bool",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bool",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto lamp intensity control is boolean 0 or 1");
}
