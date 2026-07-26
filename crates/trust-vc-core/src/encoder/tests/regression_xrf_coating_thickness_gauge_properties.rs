// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// X-ray fluorescence (XRF) coating thickness gauge properties:
// Non-contact measurement of coating thickness using characteristic X-ray emission.

#[test]
fn test_thickness_range_bounded() {
    // Thickness in ×10 μm: 500.0 μm = 5000, valid [1, 50000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rv", "range_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert("lower", "range_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "range_x10 <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thickness 500.0μm (×10) in [1, 50000]");
}

#[test]
fn test_repeatability_bounded() {
    // Repeatability in ×100 %: 0.10% = 10, valid [1, 100]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("repeat_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rv", "repeat_x100 == 10"));
    ctx.push_obligation(ProofObligation::assert("lower", "repeat_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "repeat_x100 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repeatability 0.10% (×100) in [1, 100]");
}

#[test]
fn test_measurement_time_bounded() {
    // Measurement time in seconds: 10, valid [1, 120]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tv", "time == 10"));
    ctx.push_obligation(ProofObligation::assert("lower", "time >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "time <= 120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement time 10s in [1, 120]");
}

#[test]
fn test_xray_source_disjunction() {
    // X-ray source: 1=miniature tube, 2=proportional counter, 3=PIN diode
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sv", "source == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_source",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "X-ray source miniature tube (1) in {1,2,3}");
}

#[test]
fn test_coating_type_disjunction() {
    // Coating type: 1=metallic, 2=galvanic, 3=paint, 4=anodize
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coating", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cv", "coating == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_coating",
        "coating == 1 || coating == 2 || coating == 3 || coating == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "coating type metallic (1) in {1,2,3,4}");
}

#[test]
fn test_spot_size_bounded() {
    // Spot size in ×10 mm: 1.0 mm = 10, valid [1, 100]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spot_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sv", "spot_x10 == 10"));
    ctx.push_obligation(ProofObligation::assert("lower", "spot_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "spot_x10 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spot size 1.0mm (×10) in [1, 100]");
}

#[test]
fn test_tube_voltage_bounded() {
    // Tube voltage in kV: 50, valid [5, 75]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vv", "voltage == 50"));
    ctx.push_obligation(ProofObligation::assert("lower", "voltage >= 5"));
    ctx.push_obligation(ProofObligation::assert("upper", "voltage <= 75"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube voltage 50 kV in [5, 75]");
}

#[test]
fn test_detector_type_disjunction() {
    // Detector type: 1=SDD, 2=PIN, 3=proportional
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dv", "detector == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_detector",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector type SDD (1) in {1,2,3}");
}

#[test]
fn test_operating_temp_offset() {
    // Operating temperature with +500 offset: 20°C → 520, valid [490 (-10°C), 545 (45°C)]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tv", "temp == 520"));
    ctx.push_obligation(ProofObligation::assert("lower", "temp >= 490"));
    ctx.push_obligation(ProofObligation::assert("upper", "temp <= 545"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 20°C (offset 520) in [490, 545]");
}

#[test]
fn test_collimator_selection_boolean() {
    // Collimator selection: boolean flag as i32 (1=selected, 0=not selected)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fv", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "selected",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "collimator selected (flag=1)");
}
