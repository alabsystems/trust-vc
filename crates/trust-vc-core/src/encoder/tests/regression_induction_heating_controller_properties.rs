// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn output_power_kw_bounded() {
    // Induction heating controller: output power in kW [1, 5000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pw_range",
        "power_kw >= 1 && power_kw <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert("pw_above_min", "power_kw >= 1"));
    ctx.push_obligation(ProofObligation::assert("pw_below_max", "power_kw <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Induction heater: output power in [1, 5000] kW bounded",
    );
}

#[test]
fn operating_frequency_khz_bounded() {
    // Operating frequency in kHz [1, 1000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_khz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fq_range",
        "freq_khz >= 1 && freq_khz <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("fq_above_min", "freq_khz >= 1"));
    ctx.push_obligation(ProofObligation::assert("fq_below_max", "freq_khz <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Induction heater: operating frequency in [1, 1000] kHz bounded",
    );
}

#[test]
fn application_type_four_way_disjunction() {
    // Application types: 1=hardening, 2=brazing, 3=melting, 4=forging
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("app_type", u32_ty());
    ctx.declare_var_typed("valid_app", i32_ty());
    ctx.push_obligation(ProofObligation::assume("at", "app_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_app == if app_type == 1 || app_type == 2 || app_type == 3 || app_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_app == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Induction heater: melting is valid application type (4-way)",
    );
}

#[test]
fn coil_type_three_way_disjunction() {
    // Coil types: 1=solenoid, 2=pancake, 3=split
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coil_type", u32_ty());
    ctx.declare_var_typed("valid_coil", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ct", "coil_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_coil == if coil_type == 1 || coil_type == 2 || coil_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_coil == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Induction heater: solenoid is valid coil type (3-way)",
    );
}

#[test]
fn workpiece_temperature_celsius_bounded() {
    // Workpiece temperature in degrees Celsius [200, 1600]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_c", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tc_range",
        "temp_c >= 200 && temp_c <= 1600",
    ));
    ctx.push_obligation(ProofObligation::assert("tc_above_min", "temp_c >= 200"));
    ctx.push_obligation(ProofObligation::assert("tc_below_max", "temp_c <= 1600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Induction heater: workpiece temperature in [200, 1600] C bounded",
    );
}

#[test]
fn power_supply_type_three_way_disjunction() {
    // Power supply types: 1=IGBT, 2=MOSFET, 3=thyristor
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("psu_type", u32_ty());
    ctx.declare_var_typed("valid_psu", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pt", "psu_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_psu == if psu_type == 1 || psu_type == 2 || psu_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_psu == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Induction heater: MOSFET is valid power supply type (3-way)",
    );
}

#[test]
fn cooling_water_flow_lpm_bounded() {
    // Cooling water flow rate in L/min [5, 500]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_lpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fl_range",
        "flow_lpm >= 5 && flow_lpm <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert("fl_above_min", "flow_lpm >= 5"));
    ctx.push_obligation(ProofObligation::assert("fl_below_max", "flow_lpm <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Induction heater: cooling water flow in [5, 500] L/min bounded",
    );
}

#[test]
fn efficiency_scaled_bounded() {
    // Efficiency as integer x10: 92.5% -> 925, bounded [700, 980]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ef_range",
        "eff_x10 >= 700 && eff_x10 <= 980",
    ));
    ctx.push_obligation(ProofObligation::assert("ef_above_min", "eff_x10 >= 700"));
    ctx.push_obligation(ProofObligation::assert("ef_below_max", "eff_x10 <= 980"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Induction heater: efficiency x10 in [700, 980] (70.0%-98.0%) bounded",
    );
}

#[test]
fn duty_cycle_scaled_bounded() {
    // Duty cycle as integer x10: 100.0% -> 1000, bounded [100, 1000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("duty_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dc_range",
        "duty_x10 >= 100 && duty_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert("dc_above_min", "duty_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("dc_below_max", "duty_x10 <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Induction heater: duty cycle x10 in [100, 1000] (10.0%-100.0%) bounded",
    );
}

#[test]
fn over_temperature_protection_boolean_flag() {
    // Over-temperature protection: boolean flag (i32: 1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_exceeded", i32_ty());
    ctx.declare_var_typed("protection_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("te", "temp_exceeded == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "pa_def",
        "protection_active == if temp_exceeded == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "protection_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Induction heater: temp exceeded -> protection active (boolean flag)",
    );
}
