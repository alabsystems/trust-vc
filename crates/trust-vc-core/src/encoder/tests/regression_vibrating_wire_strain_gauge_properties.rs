// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Vibrating wire strain gauge property verification.
// Encodes key parameters of a vibrating wire strain gauge and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Strain range (microstrain) — bounded [100, 10000], value 3000.
#[test]
fn test_strain_range_microstrain_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("strain_range", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sr_val", "strain_range == 3000"));
    ctx.push_obligation(ProofObligation::assert("sr_min", "strain_range >= 100"));
    ctx.push_obligation(ProofObligation::assert("sr_max", "strain_range <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "strain range 3000 microstrain in [100, 10000]");
}

/// Test 2: Resolution (x10 microstrain) — 0.1 microstrain = 1, bounded [1, 50].
#[test]
fn test_resolution_x10_microstrain_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("res_val", "res_x10 == 1"));
    ctx.push_obligation(ProofObligation::assert("res_min", "res_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("res_max", "res_x10 <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 0.1 microstrain (1 x10) in [1, 50]");
}

/// Test 3: Gauge length (mm) — bounded [50, 500], value 150.
#[test]
fn test_gauge_length_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gauge_length", u32_ty());
    ctx.push_obligation(ProofObligation::assume("gl_val", "gauge_length == 150"));
    ctx.push_obligation(ProofObligation::assert("gl_min", "gauge_length >= 50"));
    ctx.push_obligation(ProofObligation::assert("gl_max", "gauge_length <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gauge length 150 mm in [50, 500]");
}

/// Test 4: Wire material — 3-way disjunction.
/// 1=steel, 2=tungsten, 3=Inconel. Value 1 (steel).
#[test]
fn test_wire_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wire_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wm_val", "wire_material == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_wire_material",
        "wire_material == 1 || wire_material == 2 || wire_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wire material 1 (steel) is valid 3-way disjunction",
    );
}

/// Test 5: Mounting type — 3-way disjunction.
/// 1=weldable, 2=embedment, 3=surface mount. Value 2 (embedment).
#[test]
fn test_mounting_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mounting_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mt_val", "mounting_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_mounting_type",
        "mounting_type == 1 || mounting_type == 2 || mounting_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mounting type 2 (embedment) is valid 3-way disjunction",
    );
}

/// Test 6: Frequency range (Hz) — bounded [400, 6000], value 2500.
#[test]
fn test_frequency_range_hz_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", u32_ty());
    ctx.push_obligation(ProofObligation::assume("freq_val", "freq == 2500"));
    ctx.push_obligation(ProofObligation::assert("freq_min", "freq >= 400"));
    ctx.push_obligation(ProofObligation::assert("freq_max", "freq <= 6000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency range 2500 Hz in [400, 6000]");
}

/// Test 7: Cable length (m) — bounded [1, 2000], value 100.
#[test]
fn test_cable_length_m_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cable_len", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cl_val", "cable_len == 100"));
    ctx.push_obligation(ProofObligation::assert("cl_min", "cable_len >= 1"));
    ctx.push_obligation(ProofObligation::assert("cl_max", "cable_len <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cable length 100 m in [1, 2000]");
}

/// Test 8: Readout type — 3-way disjunction.
/// 1=single channel, 2=multiplexed, 3=wireless. Value 2 (multiplexed).
#[test]
fn test_readout_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("readout_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rt_val", "readout_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_readout_type",
        "readout_type == 1 || readout_type == 2 || readout_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "readout type 2 (multiplexed) is valid 3-way disjunction",
    );
}

/// Test 9: Operating temperature (deg C) — offset +500, bounded [460, 580].
/// Real range: -40 C to 80 C. Value 20 C -> 520 with offset.
#[test]
fn test_operating_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("op_temp_off", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ot_val", "op_temp_off == 520"));
    ctx.push_obligation(ProofObligation::assert("ot_min", "op_temp_off >= 460"));
    ctx.push_obligation(ProofObligation::assert("ot_max", "op_temp_off <= 580"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 20 C (offset +500: 520) in [460, 580]",
    );
}

/// Test 10: Thermistor included — boolean flag using i32.
/// Flag 1 = thermistor present. Assert derived value equals 1.
#[test]
fn test_thermistor_included_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("therm_flag", i32_ty());
    ctx.declare_var_typed("therm_present", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_is_bool",
        "therm_flag == 0 || therm_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "therm_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "therm_def",
        "therm_present == if therm_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "therm_triggered",
        "therm_present == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermistor flag activates thermistor present");
}
