// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial jet impingement dryer property verification.
// Encodes key parameters of an industrial jet impingement dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Nozzle-to-surface distance in mm — bounded range [5, 200].
#[test]
fn test_jet_impingement_dryer_nozzle_to_surface_distance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("distance", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nd_a",
        "distance >= 5 && distance <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nd_c",
        "distance >= 5 && distance <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jet impingement dryer nozzle-to-surface distance in [5, 200] mm",
    );
}

/// Jet velocity in m/s — bounded range [10, 100].
#[test]
fn test_jet_impingement_dryer_jet_velocity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "jv_a",
        "velocity >= 10 && velocity <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "jv_c",
        "velocity >= 10 && velocity <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jet impingement dryer jet velocity in [10, 100] m/s",
    );
}

/// Nozzle diameter in mm — bounded range [2, 50].
#[test]
fn test_jet_impingement_dryer_nozzle_diameter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nm_a",
        "diameter >= 2 && diameter <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nm_c",
        "diameter >= 2 && diameter <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jet impingement dryer nozzle diameter in [2, 50] mm",
    );
}

/// Surface temperature with offset +100 deg C — bounded range [120, 600].
#[test]
fn test_jet_impingement_dryer_surface_temperature() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "temp_off >= 120 && temp_off <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "temp_off >= 120 && temp_off <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jet impingement dryer surface temperature offset in [120, 600]",
    );
}

/// Air temperature with offset +100 deg C — bounded range [150, 800].
#[test]
fn test_jet_impingement_dryer_air_temperature() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_a",
        "air_temp_off >= 150 && air_temp_off <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_c",
        "air_temp_off >= 150 && air_temp_off <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jet impingement dryer air temperature offset in [150, 800]",
    );
}

/// Nozzle array rows — bounded range [1, 50].
#[test]
fn test_jet_impingement_dryer_nozzle_array_rows() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rows", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nr_a", "rows >= 1 && rows <= 50"));
    ctx.push_obligation(ProofObligation::assert("nr_c", "rows >= 1 && rows <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jet impingement dryer nozzle array rows in [1, 50]",
    );
}

/// Nozzle pattern — 3-way disjunction (1=inline, 2=staggered, 3=hexagonal).
#[test]
fn test_jet_impingement_dryer_nozzle_pattern() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pattern", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "np_a",
        "pattern == 1 || pattern == 2 || pattern == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "np_c",
        "pattern == 1 || pattern == 2 || pattern == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jet impingement dryer nozzle pattern valid 3-way disjunction",
    );
}

/// Air supply type — 3-way disjunction (1=blower, 2=compressed, 3=recirculated).
#[test]
fn test_jet_impingement_dryer_air_supply_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("supply", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "as_a",
        "supply == 1 || supply == 2 || supply == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "as_c",
        "supply == 1 || supply == 2 || supply == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jet impingement dryer air supply type valid 3-way disjunction",
    );
}

/// Heating method — 3-way disjunction (1=electric, 2=gas-fired, 3=steam).
#[test]
fn test_jet_impingement_dryer_heating_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hm_a",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hm_c",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jet impingement dryer heating method valid 3-way disjunction",
    );
}

/// Automatic temperature control — boolean flag (0 or 1).
#[test]
fn test_jet_impingement_dryer_auto_temp_control() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("tc_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jet impingement dryer auto temperature control boolean flag",
    );
}
