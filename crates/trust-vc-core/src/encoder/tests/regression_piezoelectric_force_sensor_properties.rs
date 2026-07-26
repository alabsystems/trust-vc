// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Piezoelectric force sensor property verification.
// Encodes key parameters of a piezoelectric force sensor and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Force range (N) — bounded [10, 500000].
/// Value 50000 represents 50 kN (typical mid-range force sensor).
#[test]
fn test_force_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_n", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range_val", "range_n == 50000"));
    ctx.push_obligation(ProofObligation::assert("range_min", "range_n >= 10"));
    ctx.push_obligation(ProofObligation::assert("range_max", "range_n <= 500000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "force range 50000 N in [10, 500000]");
}

/// Test 2: Sensitivity (×100 pC/N) — bounded [10, 1000].
/// Value 400 represents 4.00 pC/N (typical quartz force sensor sensitivity).
#[test]
fn test_sensitivity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sens_val", "sens_x100 == 400"));
    ctx.push_obligation(ProofObligation::assert("sens_min", "sens_x100 >= 10"));
    ctx.push_obligation(ProofObligation::assert("sens_max", "sens_x100 <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensitivity 4.00 pC/N (400 x100) in [10, 1000]");
}

/// Test 3: Resonant frequency (kHz) — bounded [5, 500].
/// Value 70 represents 70 kHz (typical mounted resonant frequency).
#[test]
fn test_resonant_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_khz", u32_ty());
    ctx.push_obligation(ProofObligation::assume("freq_val", "freq_khz == 70"));
    ctx.push_obligation(ProofObligation::assert("freq_min", "freq_khz >= 5"));
    ctx.push_obligation(ProofObligation::assert("freq_max", "freq_khz <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resonant frequency 70 kHz in [5, 500]");
}

/// Test 4: Crystal material — 3-way disjunction.
/// 1=quartz, 2=PZT, 3=gallium phosphate. Value 1 (quartz).
#[test]
fn test_crystal_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("crystal_mat", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "crystal_mat == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "crystal_mat == 1 || crystal_mat == 2 || crystal_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "crystal material 1 (quartz) is valid 3-way disjunction",
    );
}

/// Test 5: Force direction — 3-way disjunction.
/// 1=compression, 2=tension, 3=multi-component. Value 1 (compression).
#[test]
fn test_force_direction_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("force_dir", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dir_val", "force_dir == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_direction",
        "force_dir == 1 || force_dir == 2 || force_dir == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "force direction 1 (compression) is valid 3-way disjunction",
    );
}

/// Test 6: Linearity (×100 % FSO) — bounded [1, 100].
/// Value 10 represents 0.10% FSO (typical high-quality force sensor linearity).
#[test]
fn test_linearity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("linearity_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("lin_val", "linearity_x100 == 10"));
    ctx.push_obligation(ProofObligation::assert("lin_min", "linearity_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert("lin_max", "linearity_x100 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linearity 0.10% FSO (10 x100) in [1, 100]");
}

/// Test 7: Connector type — 4-way disjunction.
/// 1=BNC, 2=10-32 UNF, 3=M5, 4=integral cable. Value 2 (10-32 UNF).
#[test]
fn test_connector_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("conn_val", "conn_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_connector",
        "conn_type == 1 || conn_type == 2 || conn_type == 3 || conn_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "connector type 2 (10-32 UNF) is valid 4-way disjunction",
    );
}

/// Test 8: Stiffness (N/um) — bounded [50, 10000].
/// Value 1000 represents 1000 N/um (typical quartz force sensor stiffness).
#[test]
fn test_stiffness_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stiffness", u32_ty());
    ctx.push_obligation(ProofObligation::assume("stiff_val", "stiffness == 1000"));
    ctx.push_obligation(ProofObligation::assert("stiff_min", "stiffness >= 50"));
    ctx.push_obligation(ProofObligation::assert("stiff_max", "stiffness <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stiffness 1000 N/um in [50, 10000]");
}

/// Test 9: Operating temperature (offset +500 deg C) — bounded [440, 650].
/// Value 520 represents 20 C. Min 440 = -60 C, max 650 = 150 C.
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_offset == 520"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp_offset >= 440"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp_offset <= 650"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 20 C (offset 520) in [440, 650]");
}

/// Test 10: IEPE powered — boolean flag using i32 with if/else pattern.
/// Flag 1 = IEPE (Integrated Electronics Piezo-Electric) powered sensor.
#[test]
fn test_iepe_powered_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("iepe_flag", i32_ty());
    ctx.declare_var_typed("iepe_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "iepe_flag == 0 || iepe_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "iepe_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "active_def",
        "iepe_active == if iepe_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "iepe_is_active",
        "iepe_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEPE powered flag enables active sensor output");
}
