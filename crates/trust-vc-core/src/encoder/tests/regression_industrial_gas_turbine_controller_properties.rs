// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial gas turbine controller property verification.
// Encodes key parameters of a gas turbine power generation system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Power output (MW) — generation capacity bounded [5, 500], value 100.
#[test]
fn test_power_output_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_mw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("power_val", "power_mw == 100"));
    ctx.push_obligation(ProofObligation::assert("power_min", "power_mw >= 5"));
    ctx.push_obligation(ProofObligation::assert("power_max", "power_mw <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power output 100 MW in [5, 500]");
}

/// Test 2: Turbine inlet temperature (deg C) — TIT bounded [900, 1700], value 1400.
#[test]
fn test_turbine_inlet_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tit_degc", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tit_val", "tit_degc == 1400"));
    ctx.push_obligation(ProofObligation::assert("tit_min", "tit_degc >= 900"));
    ctx.push_obligation(ProofObligation::assert("tit_max", "tit_degc <= 1700"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "turbine inlet temp 1400 C in [900, 1700]");
}

/// Test 3: Compressor pressure ratio (x10) — bounded [80, 350], value 200 (20.0:1).
#[test]
fn test_compressor_ratio_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ratio_val", "ratio_x10 == 200"));
    ctx.push_obligation(ProofObligation::assert("ratio_min", "ratio_x10 >= 80"));
    ctx.push_obligation(ProofObligation::assert("ratio_max", "ratio_x10 <= 350"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "compressor ratio 20.0:1 (200 x10) in [80, 350]");
}

/// Test 4: Fuel type — 4-way disjunction.
/// 1=natural gas, 2=diesel, 3=dual fuel, 4=syngas. Value 1 (natural gas).
#[test]
fn test_fuel_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fuel_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fuel_val", "fuel_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_fuel",
        "fuel_type == 1 || fuel_type == 2 || fuel_type == 3 || fuel_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fuel type 1 (natural gas) is valid 4-way disjunction",
    );
}

/// Test 5: Turbine class — 4-way non-sequential disjunction (MW ratings).
/// Valid classes: 5, 50, 200, 500. Value 200.
#[test]
fn test_turbine_class_non_sequential_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("turbine_class", u32_ty());
    ctx.push_obligation(ProofObligation::assume("class_val", "turbine_class == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_class",
        "turbine_class == 5 || turbine_class == 50 || turbine_class == 200 || turbine_class == 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "turbine class 200 MW is valid (5, 50, 200, or 500)",
    );
}

/// Test 6: Heat rate (kJ/kWh) — thermal efficiency bounded [7000, 12000], value 9000.
#[test]
fn test_heat_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hr_val", "heat_rate == 9000"));
    ctx.push_obligation(ProofObligation::assert("hr_min", "heat_rate >= 7000"));
    ctx.push_obligation(ProofObligation::assert("hr_max", "heat_rate <= 12000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heat rate 9000 kJ/kWh in [7000, 12000]");
}

/// Test 7: Exhaust temperature (deg C) — bounded [400, 650], value 550.
#[test]
fn test_exhaust_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("exhaust_degc", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "exhaust_val",
        "exhaust_degc == 550",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "exhaust_min",
        "exhaust_degc >= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "exhaust_max",
        "exhaust_degc <= 650",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "exhaust temp 550 C in [400, 650]");
}

/// Test 8: Starting mode — 3-way disjunction.
/// 1=electric, 2=diesel, 3=pneumatic. Value 1 (electric).
#[test]
fn test_starting_mode_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("start_mode", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "start_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_mode",
        "start_mode == 1 || start_mode == 2 || start_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "starting mode 1 (electric) is valid 3-way disjunction",
    );
}

/// Test 9: Shaft configuration — 3-way disjunction.
/// 1=single-shaft, 2=two-shaft, 3=three-shaft. Value 2 (two-shaft).
#[test]
fn test_shaft_config_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shaft_config", u32_ty());
    ctx.push_obligation(ProofObligation::assume("shaft_val", "shaft_config == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_shaft",
        "shaft_config == 1 || shaft_config == 2 || shaft_config == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shaft config 2 (two-shaft) is valid 3-way disjunction",
    );
}

/// Test 10: NOx control — boolean flag using i32 with if/else pattern.
/// Flag 1 = DLN (dry low NOx) enabled, which limits TIT to 1500 C.
#[test]
fn test_nox_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dln_flag", i32_ty());
    ctx.declare_var_typed("tit_limit", u32_ty());
    ctx.declare_var_typed("effective_tit", u32_ty());
    ctx.declare_var_typed("max_tit", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "dln_flag == 1"));
    ctx.push_obligation(ProofObligation::assume("max_tit_val", "max_tit == 1700"));
    ctx.push_obligation(ProofObligation::assume("limit_val", "tit_limit == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "effective_def",
        "effective_tit == if dln_flag == 1 { tit_limit } else { max_tit }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dln_tit_limited",
        "effective_tit <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DLN flag limits effective TIT to 1500 C");
}
