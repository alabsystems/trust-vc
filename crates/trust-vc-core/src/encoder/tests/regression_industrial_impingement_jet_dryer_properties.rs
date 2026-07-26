// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_impingement_jet_velocity_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jet_vel_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "jv_a",
        "jet_vel_x10 >= 50 && jet_vel_x10 <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "jv_c",
        "jet_vel_x10 >= 50 && jet_vel_x10 <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jet velocity x10 in [50, 1500] representing 5.0-150.0 m/s",
    );
}

#[test]
fn test_impingement_nozzle_distance_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("standoff_mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sd_a",
        "standoff_mm >= 5 && standoff_mm <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sd_c",
        "standoff_mm >= 5 && standoff_mm <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nozzle-to-substrate distance in [5, 200] mm");
}

#[test]
fn test_impingement_air_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_a",
        "air_temp >= 60 && air_temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_c",
        "air_temp >= 60 && air_temp <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "supply air temperature in [60, 500] C");
}

#[test]
fn test_impingement_substrate_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("web_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ws_a",
        "web_speed >= 1 && web_speed <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ws_c",
        "web_speed >= 1 && web_speed <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "substrate web speed in [1, 3000] m/min");
}

#[test]
fn test_impingement_nozzle_pitch_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nozzle_pitch", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "np_a",
        "nozzle_pitch >= 10 && nozzle_pitch <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "np_c",
        "nozzle_pitch >= 10 && nozzle_pitch <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nozzle pitch in [10, 300] mm");
}

#[test]
fn test_impingement_open_area_ratio_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("open_area_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oa_a",
        "open_area_x100 >= 1 && open_area_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oa_c",
        "open_area_x100 >= 1 && open_area_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "open area ratio x100 in [1, 5000]");
}

#[test]
fn test_impingement_nozzle_geometry_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noz_geom", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ng_a",
        "noz_geom == 1 || noz_geom == 2 || noz_geom == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ng_c",
        "noz_geom == 1 || noz_geom == 2 || noz_geom == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nozzle geometry: round orifice, slot jet, or shaped contour",
    );
}

#[test]
fn test_impingement_exhaust_return_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("exhaust_ret", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "er_a",
        "exhaust_ret == 1 || exhaust_ret == 2 || exhaust_ret == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "er_c",
        "exhaust_ret == 1 || exhaust_ret == 2 || exhaust_ret == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "exhaust return: side, through-nozzle, or bottom extraction",
    );
}

#[test]
fn test_impingement_substrate_support_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sub_support", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ss_a",
        "sub_support == 1 || sub_support == 2 || sub_support == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ss_c",
        "sub_support == 1 || sub_support == 2 || sub_support == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "substrate support: air flotation, roll, or belt conveyor",
    );
}

#[test]
fn test_impingement_oscillating_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oscillating", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "osc_a",
        "oscillating == 0 || oscillating == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "osc_c",
        "oscillating == 0 || oscillating == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "oscillating nozzle flag is boolean");
}
