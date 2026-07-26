// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn wavelength_range_min_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_min", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wl_min_range",
        "wl_min >= 300 && wl_min <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wl_min_positive",
        "wl_min >= 300 && wl_min <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength range min should be in [300, 400] nm");
}

#[test]
fn wavelength_range_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wl_max_range",
        "wl_max >= 700 && wl_max <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wl_max_valid",
        "wl_max >= 700 && wl_max <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength range max should be in [700, 800] nm");
}

#[test]
fn spectral_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_range",
        "resolution >= 1 && resolution <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_valid",
        "resolution >= 1 && resolution <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectral resolution should be in [1, 20] nm");
}

#[test]
fn geometry_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geometry", i32_ty());
    // 1=d/8° sphere, 2=45°/0°, 3=multi-angle, 4=inline
    ctx.push_obligation(ProofObligation::assume(
        "geometry_valid",
        "geometry == 1 || geometry == 2 || geometry == 3 || geometry == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "geometry_in_range",
        "geometry >= 1 && geometry <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "geometry type 4-way disjunction implies bounded [1, 4]",
    );
}

#[test]
fn light_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    // 1=xenon, 2=LED, 3=tungsten halogen
    ctx.push_obligation(ProofObligation::assume(
        "source_valid",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "source_in_range",
        "source >= 1 && source <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "light source 3-way disjunction implies bounded [1, 3]",
    );
}

#[test]
fn repeatability_scaled_bounded() {
    // Repeatability in ΔE × 10000: e.g., 0.0100 → 100
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("repeatability", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "repeatability_range",
        "repeatability >= 1 && repeatability <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "repeatability_positive",
        "repeatability >= 1 && repeatability <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repeatability (x10000 DE) should be in [1, 500]");
}

#[test]
fn aperture_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("aperture", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aperture_range",
        "aperture >= 1 && aperture <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aperture_valid",
        "aperture >= 1 && aperture <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "aperture size should be in [1, 50] mm");
}

#[test]
fn measurement_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "meas_time_range",
        "meas_time >= 100 && meas_time <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "meas_time_valid",
        "meas_time >= 100 && meas_time <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement time should be in [100, 10000] ms");
}

#[test]
fn operating_temp_offset_bounded() {
    // Temperature offset by +500: e.g., -50°C → 450, 80°C → 580
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_offset_range",
        "temp_offset >= 450 && temp_offset <= 580",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_offset_valid",
        "temp_offset >= 450 && temp_offset <= 580",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp (offset +500) should be in [450, 580]",
    );
}

#[test]
fn uv_filter_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("uv_filter", i32_ty());
    ctx.declare_var_typed("mode", i32_ty());
    // Boolean flag: 0 = no UV filter, 1 = UV filter present
    ctx.push_obligation(ProofObligation::assume(
        "uv_filter_bool",
        "uv_filter == 0 || uv_filter == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "mode_def",
        "mode == if uv_filter == 1 { 10 } else { 20 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "mode == 10 || mode == 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "UV filter boolean flag selects between two modes");
}
