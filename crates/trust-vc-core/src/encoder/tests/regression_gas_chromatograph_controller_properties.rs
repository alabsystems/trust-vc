// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Gas chromatograph controller property verification.
// Encodes key parameters of a GC instrument and verifies
// that they satisfy bounded, scaled, disjunctive, and boolean-flag constraints.

/// Test 1: Oven temperature max (offset +500) — 450 deg C encoded as 950, bounded [500, 1150].
/// Offset +500 maps [-500, +650] C to unsigned [0, 1150].
/// 500 = 0 C, 950 = 450 C, 1150 = 650 C.
#[test]
fn test_oven_temp_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oven_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "oven_temp == 950")); // 450 C
    ctx.push_obligation(ProofObligation::assert("temp_lower", "oven_temp >= 500")); // 0 C
    ctx.push_obligation(ProofObligation::assert("temp_upper", "oven_temp <= 1150")); // 650 C
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "oven temp 450 C (950 offset+500) in [500, 1150]");
}

/// Test 2: Oven ramp rate (x10 deg C/min) — 200 represents 20.0 deg C/min, bounded [1, 1200].
/// Scale x10 gives 0.1 deg C/min resolution. Range: 0.1 to 120.0 deg C/min.
#[test]
fn test_oven_ramp_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ramp_rate_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ramp_val", "ramp_rate_x10 == 200")); // 20.0 C/min
    ctx.push_obligation(ProofObligation::assert("ramp_lower", "ramp_rate_x10 >= 1")); // 0.1 C/min
    ctx.push_obligation(ProofObligation::assert(
        "ramp_upper",
        "ramp_rate_x10 <= 1200",
    )); // 120.0 C/min
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "oven ramp rate 20.0 C/min (200 x10) in [1, 1200]");
}

/// Test 3: Column length (m) — 30 m column, bounded [5, 100].
#[test]
fn test_column_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("column_length_m", u32_ty());
    ctx.push_obligation(ProofObligation::assume("col_val", "column_length_m == 30"));
    ctx.push_obligation(ProofObligation::assert("col_lower", "column_length_m >= 5"));
    ctx.push_obligation(ProofObligation::assert(
        "col_upper",
        "column_length_m <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column length 30 m in [5, 100]");
}

/// Test 4: Column inner diameter (x1000 mm) — 250 represents 0.250 mm, bounded [100, 530].
/// Scale x1000 gives 0.001 mm resolution. Range: 0.100 to 0.530 mm.
#[test]
fn test_column_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("col_id_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume("id_val", "col_id_x1000 == 250")); // 0.250 mm
    ctx.push_obligation(ProofObligation::assert("id_lower", "col_id_x1000 >= 100")); // 0.100 mm
    ctx.push_obligation(ProofObligation::assert("id_upper", "col_id_x1000 <= 530")); // 0.530 mm
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "column ID 0.250 mm (250 x1000) in [100, 530]");
}

/// Test 5: Carrier gas flow rate (x10 mL/min) — 12 represents 1.2 mL/min, bounded [1, 200].
/// Scale x10 gives 0.1 mL/min resolution. Range: 0.1 to 20.0 mL/min.
#[test]
fn test_carrier_gas_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_x10 == 12")); // 1.2 mL/min
    ctx.push_obligation(ProofObligation::assert("flow_lower", "flow_x10 >= 1")); // 0.1 mL/min
    ctx.push_obligation(ProofObligation::assert("flow_upper", "flow_x10 <= 200")); // 20.0 mL/min
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "carrier gas flow 1.2 mL/min (12 x10) in [1, 200]");
}

/// Test 6: Detector type — 3-way disjunction: 1=FID, 2=TCD, 3=ECD.
#[test]
fn test_detector_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("det_val", "detector_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_detector",
        "detector_type == 1 || detector_type == 2 || detector_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type 1 (FID) is valid 3-way disjunction {1=FID, 2=TCD, 3=ECD}",
    );
}

/// Test 7: Injection mode — 3-way disjunction: 1=split, 2=splitless, 3=on-column.
#[test]
fn test_injection_mode_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("injection_mode", u32_ty());
    ctx.push_obligation(ProofObligation::assume("inj_val", "injection_mode == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_injection",
        "injection_mode == 1 || injection_mode == 2 || injection_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "injection mode 2 (splitless) is valid 3-way disjunction {1=split, 2=splitless, 3=on-column}",
    );
}

/// Test 8: Carrier gas — 3-way disjunction: 1=helium, 2=nitrogen, 3=hydrogen.
#[test]
fn test_carrier_gas_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("carrier_gas", u32_ty());
    ctx.push_obligation(ProofObligation::assume("gas_val", "carrier_gas == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_gas",
        "carrier_gas == 1 || carrier_gas == 2 || carrier_gas == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "carrier gas 3 (hydrogen) is valid 3-way disjunction {1=helium, 2=nitrogen, 3=hydrogen}",
    );
}

/// Test 9: Sample capacity — number of vials, bounded [1, 120], value 96.
#[test]
fn test_sample_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_capacity", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cap_val", "sample_capacity == 96"));
    ctx.push_obligation(ProofObligation::assert("cap_lower", "sample_capacity >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "cap_upper",
        "sample_capacity <= 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample capacity 96 vials in [1, 120]");
}

/// Test 10: Autosampler enabled — boolean flag using i32 with if/else pattern.
/// Flag 1 = autosampler present, autosampler_active = 1.
#[test]
fn test_autosampler_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("autosampler_flag", i32_ty());
    ctx.declare_var_typed("autosampler_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "autosampler_flag == 0 || autosampler_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "autosampler_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "active_def",
        "autosampler_active == if autosampler_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "autosampler_enabled",
        "autosampler_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "autosampler flag enables automatic sample injection",
    );
}
