// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn maldi_mass_range_kda() {
    // MALDI mass range: 1-1000 kDa
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass_kda", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "mass_kda >= 1 && mass_kda <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "mass_kda == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "mass_kda >= 1 && mass_kda <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MALDI: 150 kDa in [1, 1000]");
}

#[test]
fn maldi_mass_resolution() {
    // Mass resolution m/delta_m: 1000-100000
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "resolution >= 1000 && resolution <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "resolution == 20000"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "resolution >= 1000 && resolution <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MALDI: resolution 20000 in [1000, 100000]");
}

#[test]
fn maldi_laser_repetition_rate_hz() {
    // Laser repetition rate: 1-10000 Hz
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rep_rate_hz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "rep_rate_hz >= 1 && rep_rate_hz <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "rep_rate_hz == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "rep_rate_hz >= 1 && rep_rate_hz <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MALDI: laser rep rate 2000 Hz in [1, 10000]");
}

#[test]
fn maldi_spot_size_scaled() {
    // Spot size in x10 um: 10-2000 (representing 1.0-200.0 um)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spot_size_x10um", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "spot_size_x10um >= 10 && spot_size_x10um <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "spot_size_x10um == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "spot_size_x10um >= 10 && spot_size_x10um <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MALDI: spot size 50.0 um (500 x10) in [1.0, 200.0]",
    );
}

#[test]
fn maldi_accelerating_voltage_kv() {
    // Accelerating voltage: 1-30 kV
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_kv", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "voltage_kv >= 1 && voltage_kv <= 30",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "voltage_kv == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "voltage_kv >= 1 && voltage_kv <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MALDI: accelerating voltage 20 kV in [1, 30]");
}

#[test]
fn maldi_laser_type_disjunction() {
    // Laser type: 1=nitrogen, 2=Nd-YAG, 3=smartbeam
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "laser_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "laser_type == 1 || laser_type == 2 || laser_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MALDI: laser type Nd-YAG (2) in {nitrogen, Nd-YAG, smartbeam}",
    );
}

#[test]
fn maldi_analyzer_type_disjunction() {
    // Analyzer type: 1=TOF-linear, 2=TOF-reflectron, 3=TOF-TOF
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "analyzer_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "analyzer_type == 1 || analyzer_type == 2 || analyzer_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MALDI: analyzer TOF-TOF (3) in {linear, reflectron, TOF-TOF}",
    );
}

#[test]
fn maldi_sample_plate_type_disjunction() {
    // Sample plate type: 1=ground-steel, 2=anchor-chip, 3=SCOUT
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plate_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "plate_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "plate_type == 1 || plate_type == 2 || plate_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MALDI: plate ground-steel (1) in {ground-steel, anchor-chip, SCOUT}",
    );
}

#[test]
fn maldi_mass_accuracy_scaled() {
    // Mass accuracy in x10 ppm: 1-100 (representing 0.1-10.0 ppm)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10ppm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "accuracy_x10ppm >= 1 && accuracy_x10ppm <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "accuracy_x10ppm == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "accuracy_x10ppm >= 1 && accuracy_x10ppm <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MALDI: mass accuracy 3.0 ppm (30 x10) in [0.1, 10.0]",
    );
}

#[test]
fn maldi_delayed_extraction_flag() {
    // Delayed extraction: boolean flag (i32: 1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("delayed_extraction", i32_ty());
    ctx.declare_var_typed("de_enabled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "delayed_extraction == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "de_def",
        "de_enabled == if delayed_extraction == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("enabled", "de_enabled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MALDI: delayed extraction enabled");
}
