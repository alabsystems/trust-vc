// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ti_sub_filament_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fil_current_a", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fc_a",
        "fil_current_a >= 30 && fil_current_a <= 55",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fc_c",
        "fil_current_a >= 30 && fil_current_a <= 55",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filament current in [30, 55] A");
}

#[test]
fn test_ti_sub_deposition_time_sec_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dep_time_s", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "dep_time_s >= 30 && dep_time_s <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "dep_time_s >= 30 && dep_time_s <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "deposition time in [30, 600] seconds");
}

#[test]
fn test_ti_sub_base_pressure_torr_x1000000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p_x1e6", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bp_a",
        "p_x1e6 >= 1 && p_x1e6 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bp_c",
        "p_x1e6 >= 1 && p_x1e6 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "base pressure x1e6 in [1, 100000] representing 1e-6 to 0.1 Torr",
    );
}

#[test]
fn test_ti_sub_pumping_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_lps", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ps_a",
        "speed_lps >= 100 && speed_lps <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ps_c",
        "speed_lps >= 100 && speed_lps <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pumping speed in [100, 100000] L/s");
}

#[test]
fn test_ti_sub_filament_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fil_count", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fn_a",
        "fil_count >= 1 && fil_count <= 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fn_c",
        "fil_count >= 1 && fil_count <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filament count in [1, 4]");
}

#[test]
fn test_ti_sub_surface_area_cm2_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("surf_cm2", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sa_a",
        "surf_cm2 >= 100 && surf_cm2 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sa_c",
        "surf_cm2 >= 100 && surf_cm2 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "deposition surface area in [100, 50000] cm^2");
}

#[test]
fn test_ti_sub_gas_species_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gs_a",
        "gas_spec == 1 || gas_spec == 2 || gas_spec == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gs_c",
        "gas_spec == 1 || gas_spec == 2 || gas_spec == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "target gas: hydrogen, nitrogen, or oxygen");
}

#[test]
fn test_ti_sub_geometry_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geometry", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gm_a",
        "geometry == 1 || geometry == 2 || geometry == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gm_c",
        "geometry == 1 || geometry == 2 || geometry == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "geometry: ball source, filament cartridge, or planar magnetron",
    );
}

#[test]
fn test_ti_sub_controller_mode_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cm_a",
        "ctrl_mode == 1 || ctrl_mode == 2 || ctrl_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cm_c",
        "ctrl_mode == 1 || ctrl_mode == 2 || ctrl_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "controller: timed, pressure-triggered, or continuous",
    );
}

#[test]
fn test_ti_sub_interlock_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("interlock", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "il_a",
        "interlock == 0 || interlock == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "il_c",
        "interlock == 0 || interlock == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure interlock flag is boolean");
}
