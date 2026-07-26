// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_gdms_mass_range_amu_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_mass",
        "mass >= 1 && mass <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_mass",
        "mass >= 1 && mass <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range bounded 1-300 amu");
}

#[test]
fn test_gdms_discharge_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_voltage",
        "voltage >= 200 && voltage <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_voltage",
        "voltage >= 200 && voltage <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge voltage bounded 200-2000 V");
}

#[test]
fn test_gdms_discharge_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_curr",
        "curr_x100 >= 1 && curr_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_curr",
        "curr_x100 >= 1 && curr_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge current x100 bounded 0.01-50.00 mA");
}

#[test]
fn test_gdms_argon_pressure_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_press",
        "press_x1000 >= 1 && press_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_press",
        "press_x1000 >= 1 && press_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "argon pressure x1000 bounded 0.001-10.000 torr");
}

#[test]
fn test_gdms_source_temperature_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_temp",
        "temp_off >= 80 && temp_off <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_temp",
        "temp_off >= 80 && temp_off <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "source temperature offset+100 bounded representing -20 to 200 C",
    );
}

#[test]
fn test_gdms_resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_res",
        "res_x10 >= 100 && res_x10 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_res",
        "res_x10 >= 100 && res_x10 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "resolution x10 bounded 10.0-10000.0 resolving power",
    );
}

#[test]
fn test_gdms_discharge_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_mode",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_mode",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge mode three-way: DC, RF, or pulsed");
}

#[test]
fn test_gdms_gas_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_gas",
        "gas == 1 || gas == 2 || gas == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_gas",
        "gas == 1 || gas == 2 || gas == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "gas type three-way: argon, neon, or krypton");
}

#[test]
fn test_gdms_analyzer_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_analyzer",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_analyzer",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analyzer three-way: double-focusing, quadrupole, or TOF",
    );
}

#[test]
fn test_gdms_auto_sputtering_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_flag",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_flag",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto sputtering control flag is boolean");
}
