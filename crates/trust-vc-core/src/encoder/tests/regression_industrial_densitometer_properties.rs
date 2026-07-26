// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial densitometer property verification.
// Encodes key parameters of an industrial process densitometer and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Density range (×1000 kg/m³) — bounded [500, 5000].
/// 1250 represents 1.250 kg/m³. Value 1250 (typical liquid density).
#[test]
fn test_density_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("density_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dens_val", "density_x1000 == 1250"));
    ctx.push_obligation(ProofObligation::assert("dens_min", "density_x1000 >= 500"));
    ctx.push_obligation(ProofObligation::assert("dens_max", "density_x1000 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "density 1.250 kg/m3 (1250 x1000) in [500, 5000]");
}

/// Test 2: Accuracy (×10000 kg/m³) — bounded [1, 100].
/// 1 represents 0.0001 kg/m³. Value 5 (0.0005 kg/m³ typical accuracy).
#[test]
fn test_accuracy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10000", u32_ty());
    ctx.push_obligation(ProofObligation::assume("acc_val", "accuracy_x10000 == 5"));
    ctx.push_obligation(ProofObligation::assert("acc_min", "accuracy_x10000 >= 1"));
    ctx.push_obligation(ProofObligation::assert("acc_max", "accuracy_x10000 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 0.0005 kg/m3 (5 x10000) in [1, 100]");
}

/// Test 3: Measurement type — 3-way disjunction.
/// 1=vibrating tube, 2=Coriolis, 3=nuclear. Value 1 (vibrating tube).
#[test]
fn test_measurement_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("meas_val", "meas_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_meas",
        "meas_type == 1 || meas_type == 2 || meas_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement type 1 (vibrating tube) is valid 3-way disjunction",
    );
}

/// Test 4: Process pressure (kPa) — bounded [100, 40000].
/// Value 10000 (10 MPa typical process pressure).
#[test]
fn test_process_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_kpa", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_val",
        "pressure_kpa == 10000",
    ));
    ctx.push_obligation(ProofObligation::assert("press_min", "pressure_kpa >= 100"));
    ctx.push_obligation(ProofObligation::assert(
        "press_max",
        "pressure_kpa <= 40000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "process pressure 10000 kPa in [100, 40000]");
}

/// Test 5: Process temperature offset +500 (deg C) — bounded [250, 1000].
/// 250 represents -250 C, 1000 represents 500 C. Value 520 (20 C).
#[test]
fn test_process_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("proc_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_val",
        "proc_temp_offset == 520",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_min",
        "proc_temp_offset >= 250",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_max",
        "proc_temp_offset <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "process temp 20 C (offset 520) in [250, 1000]");
}

/// Test 6: Sample volume (mL) — bounded [1, 100].
/// Value 2 (2 mL typical vibrating tube sample volume).
#[test]
fn test_sample_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_ml", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vol_val", "sample_ml == 2"));
    ctx.push_obligation(ProofObligation::assert("vol_min", "sample_ml >= 1"));
    ctx.push_obligation(ProofObligation::assert("vol_max", "sample_ml <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample volume 2 mL in [1, 100]");
}

/// Test 7: Output type — 4-way disjunction.
/// 1=4-20mA, 2=HART, 3=Modbus, 4=Profibus. Value 2 (HART).
#[test]
fn test_output_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("out_val", "output_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_output",
        "output_type == 1 || output_type == 2 || output_type == 3 || output_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type 2 (HART) is valid 4-way disjunction");
}

/// Test 8: Response time (s) — bounded [1, 120].
/// Value 10 (10 seconds typical response time).
#[test]
fn test_response_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("response_s", u32_ty());
    ctx.push_obligation(ProofObligation::assume("resp_val", "response_s == 10"));
    ctx.push_obligation(ProofObligation::assert("resp_min", "response_s >= 1"));
    ctx.push_obligation(ProofObligation::assert("resp_max", "response_s <= 120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time 10 s in [1, 120]");
}

/// Test 9: Wetted material — 3-way disjunction.
/// 1=stainless 316L, 2=Hastelloy C, 3=tantalum. Value 1 (stainless 316L).
#[test]
fn test_wetted_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wetted_mat", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "wetted_mat == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "wetted_mat == 1 || wetted_mat == 2 || wetted_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wetted material 1 (stainless 316L) is valid 3-way disjunction",
    );
}

/// Test 10: Viscosity correction — boolean flag using i32 with if/else pattern.
/// Flag 1 = viscosity correction enabled, corrected_reading = 1.
#[test]
fn test_viscosity_correction_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("visc_corr_flag", i32_ty());
    ctx.declare_var_typed("corrected_reading", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "visc_corr_flag == 0 || visc_corr_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "visc_corr_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "corr_def",
        "corrected_reading == if visc_corr_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "correction_active",
        "corrected_reading == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "viscosity correction flag enables corrected reading",
    );
}
