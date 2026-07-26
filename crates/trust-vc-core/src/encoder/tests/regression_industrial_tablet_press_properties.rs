// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Industrial tablet press (rotary tablet compression) verification properties.

use super::*;

#[test]
fn test_station_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stations", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "stations >= 8 && stations <= 75",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "stations == 45"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "stations >= 8 && stations <= 75",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "punch station count within rotary press range 8-75",
    );
}

#[test]
fn test_max_force_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("force_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "force_x10 >= 10 && force_x10 <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "force_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "force_x10 >= 10 && force_x10 <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "max compression force x10 kN within range 10-1500 (100.0 kN)",
    );
}

#[test]
fn test_output_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "rate >= 10000 && rate <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "rate == 500000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "rate >= 10000 && rate <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tablet output rate within range 10000-1000000 tablets/hour",
    );
}

#[test]
fn test_turret_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "speed_x10 >= 10 && speed_x10 <= 1200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "speed_x10 == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "speed_x10 >= 10 && speed_x10 <= 1200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "turret speed x10 RPM within range 10-1200 (60.0 RPM)",
    );
}

#[test]
fn test_tablet_diameter_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "diameter_x10 >= 20 && diameter_x10 <= 250",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "diameter_x10 == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "diameter_x10 >= 20 && diameter_x10 <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tablet diameter x10 mm within range 20-250 (10.0 mm)",
    );
}

#[test]
fn test_fill_depth_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "depth_x10 >= 10 && depth_x10 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "depth_x10 == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "depth_x10 >= 10 && depth_x10 <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "die fill depth x10 mm within range 10-300 (15.0 mm)",
    );
}

#[test]
fn test_tooling_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tooling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "tooling >= 1 && tooling <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "tooling == 1 || tooling == 2 || tooling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tooling type is B-type(1) or D-type(2) or custom(3)",
    );
}

#[test]
fn test_compression_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("compression", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "compression >= 1 && compression <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "compression == 1 || compression == 2 || compression == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compression type is single-layer(1) or bi-layer(2) or tri-layer(3)",
    );
}

#[test]
fn test_force_feeder_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feeder", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "feeder >= 1 && feeder <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "feeder == 1 || feeder == 2 || feeder == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "force feeder type is gravity(1) or paddle(2) or centrifugal(3)",
    );
}

#[test]
fn test_precompression_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "enabled",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "precompression enabled when flag is 1");
}
