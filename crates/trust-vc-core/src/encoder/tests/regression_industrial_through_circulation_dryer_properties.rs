// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// ---------------------------------------------------------------------------
// Industrial through-circulation dryer – property-based regression tests
// ---------------------------------------------------------------------------

/// Bed depth in mm — bounded range.
#[test]
fn test_through_circulation_dryer_bed_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bd_a",
        "depth >= 10 && depth <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bd_c",
        "depth >= 10 && depth <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "through-circulation dryer bed depth bounded");
}

/// Air velocity at ×10 m/s — bounded range.
#[test]
fn test_through_circulation_dryer_air_velocity_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vel_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "av_a",
        "vel_x10 >= 1 && vel_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "av_c",
        "vel_x10 >= 1 && vel_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "through-circulation dryer air velocity x10 bounded",
    );
}

/// Belt speed at ×100 m/min — bounded range.
#[test]
fn test_through_circulation_dryer_belt_speed_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bs_a",
        "speed_x100 >= 1 && speed_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bs_c",
        "speed_x100 >= 1 && speed_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "through-circulation dryer belt speed x100 bounded");
}

/// Air temperature with offset +100 °C — bounded range.
#[test]
fn test_through_circulation_dryer_air_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_a",
        "temp_off >= 120 && temp_off <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_c",
        "temp_off >= 120 && temp_off <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "through-circulation dryer air temperature offset bounded",
    );
}

/// Belt width in mm — bounded range.
#[test]
fn test_through_circulation_dryer_belt_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bw_a",
        "width >= 500 && width <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bw_c",
        "width >= 500 && width <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "through-circulation dryer belt width bounded");
}

/// Air flow direction — 3-way disjunction.
#[test]
fn test_through_circulation_dryer_air_flow_direction_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dir", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fd_a",
        "dir == 1 || dir == 2 || dir == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fd_c",
        "dir == 1 || dir == 2 || dir == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "through-circulation dryer air flow direction three-way disjunction",
    );
}

/// Belt material — 3-way disjunction.
#[test]
fn test_through_circulation_dryer_belt_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bm_a",
        "bm == 1 || bm == 2 || bm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bm_c",
        "bm == 1 || bm == 2 || bm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "through-circulation dryer belt material three-way disjunction",
    );
}

/// Heating source — 3-way disjunction.
#[test]
fn test_through_circulation_dryer_heating_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hs", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hs_a",
        "hs == 1 || hs == 2 || hs == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hs_c",
        "hs == 1 || hs == 2 || hs == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "through-circulation dryer heating source three-way disjunction",
    );
}

/// Automatic humidity control — boolean flag.
#[test]
fn test_through_circulation_dryer_auto_humidity_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hc_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("hc_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "through-circulation dryer auto humidity control flag",
    );
}

/// Zone count — bounded range.
#[test]
fn test_through_circulation_dryer_zone_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zones", i32_ty());
    ctx.push_obligation(ProofObligation::assume("zc_a", "zones >= 1 && zones <= 20"));
    ctx.push_obligation(ProofObligation::assert("zc_c", "zones >= 1 && zones <= 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "through-circulation dryer zone count bounded");
}
