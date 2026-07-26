// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Canned motor pump controller verification properties.
/// Models key parameters of hermetically sealed canned motor pumps
/// used in hazardous/leak-free process applications.

// 1. Flow rate scaled x10 (m^3/h), range 1-5000 => 0.1-500.0 m^3/h
#[test]
fn test_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 50.0 m3/h (500 x10) in [1, 5000]");
}

// 2. Pump head scaled x10 (m), range 10-2000 => 1.0-200.0 m
#[test]
fn test_head_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "head_range",
        "head_x10 >= 10 && head_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assume("head_val", "head_x10 == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "head_bounded",
        "head_x10 >= 10 && head_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "head 80.0 m (800 x10) in [10, 2000]");
}

// 3. Motor power scaled x10 (kW), range 1-10000 => 0.1-1000.0 kW
#[test]
fn test_power_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pow_range",
        "pow_x10 >= 1 && pow_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("pow_val", "pow_x10 == 550"));
    ctx.push_obligation(ProofObligation::assert(
        "pow_bounded",
        "pow_x10 >= 1 && pow_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power 55.0 kW (550 x10) in [1, 10000]");
}

// 4. Motor speed (RPM), range 1000-7200
#[test]
fn test_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1000 && speed <= 7200",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 3600"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1000 && speed <= 7200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed 3600 RPM in [1000, 7200]");
}

// 5. Max process temperature with +100 offset to avoid negatives,
//    range 100-700 => 0-600 deg C actual
#[test]
fn test_max_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp >= 100 && temp <= 700",
    ));
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 100 && temp <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max temp 400 C (offset 500) in [100, 700]");
}

// 6. Max design pressure scaled x10 (bar), range 10-4000 => 1.0-400.0 bar
#[test]
fn test_max_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 10 && press_x10 <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assume("press_val", "press_x10 == 400"));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press_x10 >= 10 && press_x10 <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure 40.0 bar (400 x10) in [10, 4000]");
}

// 7. Impeller type: 1=closed, 2=semi-open, 3=inducer
#[test]
fn test_impeller_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impeller", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "impeller_valid",
        "impeller == 1 || impeller == 2 || impeller == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "impeller_in_range",
        "impeller >= 1 && impeller <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller type 3-way disjunction");
}

// 8. Winding insulation class: 1=class-F, 2=class-H, 3=class-N
#[test]
fn test_winding_insulation_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("insulation", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "insulation_valid",
        "insulation == 1 || insulation == 2 || insulation == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "insulation_in_range",
        "insulation >= 1 && insulation <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "winding insulation 3-way disjunction");
}

// 9. Bearing type: 1=sleeve, 2=thrust-disc, 3=ceramic
#[test]
fn test_bearing_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bearing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bearing_valid",
        "bearing == 1 || bearing == 2 || bearing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bearing_in_range",
        "bearing >= 1 && bearing <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bearing type 3-way disjunction");
}

// 10. Leak-free boolean flag: i32, 0 or 1; assert sealed when flag is 1
#[test]
fn test_leak_free_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leakfree", i32_ty());
    ctx.push_obligation(ProofObligation::assume("leakfree_val", "leakfree == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "sealed",
        "if leakfree == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "leak-free boolean flag");
}
