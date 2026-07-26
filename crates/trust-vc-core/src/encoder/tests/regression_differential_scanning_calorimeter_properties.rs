// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_dsc_temp_range_max_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_t", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "max_t >= 520 && max_t <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "max_t >= 520"));
    ctx.push_obligation(ProofObligation::assert("upper", "max_t <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSC: max temp offset+500 in [520, 2000]");
}

#[test]
fn test_dsc_temp_range_min_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("min_t", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "min_t >= 320 && min_t <= 525",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "min_t >= 320"));
    ctx.push_obligation(ProofObligation::assert("upper", "min_t <= 525"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSC: min temp offset+500 in [320, 525]");
}

#[test]
fn test_dsc_heating_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "hr_x10 >= 1 && hr_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "hr_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "hr_x10 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSC: heating rate x10 in [1, 5000]");
}

#[test]
fn test_dsc_cooling_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "cr_x10 >= 1 && cr_x10 <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "cr_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "cr_x10 <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSC: cooling rate x10 in [1, 3000]");
}

#[test]
fn test_dsc_sensitivity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sens_x100 >= 1 && sens_x100 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "sens_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "sens_x100 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSC: sensitivity x100 in [1, 100]");
}

#[test]
fn test_dsc_sample_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "cap >= 1 && cap <= 100"));
    ctx.push_obligation(ProofObligation::assert("lower", "cap >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "cap <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSC: sample capacity in [1, 100] mg");
}

#[test]
fn test_dsc_atmosphere_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atm", i32_ty());
    // 1=nitrogen, 2=air, 3=argon
    ctx.push_obligation(ProofObligation::assume(
        "valid_atm",
        "atm == 1 || atm == 2 || atm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_one", "atm >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_three", "atm <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DSC: atmosphere is nitrogen(1), air(2), or argon(3)",
    );
}

#[test]
fn test_dsc_sensor_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor", i32_ty());
    // 1=heat flux, 2=power compensation, 3=Calvet
    ctx.push_obligation(ProofObligation::assume(
        "valid_sensor",
        "sensor == 1 || sensor == 2 || sensor == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_one", "sensor >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_three", "sensor <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DSC: sensor is heat flux(1), power comp(2), or Calvet(3)",
    );
}

#[test]
fn test_dsc_cooling_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cool", i32_ty());
    // 1=mechanical, 2=liquid nitrogen, 3=compressed air
    ctx.push_obligation(ProofObligation::assume(
        "valid_cool",
        "cool == 1 || cool == 2 || cool == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_one", "cool >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_three", "cool <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DSC: cooling is mechanical(1), LN2(2), or compressed air(3)",
    );
}

#[test]
fn test_dsc_autosampler_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_s", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid",
        "auto_s == 0 || auto_s == 1",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_zero", "auto_s >= 0"));
    ctx.push_obligation(ProofObligation::assert("at_most_one", "auto_s <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DSC: autosampler flag is 0 or 1");
}
