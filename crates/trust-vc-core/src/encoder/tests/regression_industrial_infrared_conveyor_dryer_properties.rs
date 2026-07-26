// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn emitter_temperature_offset_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "emitter_temp_offset",
        "temp_off >= 700 && temp_off <= 1600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "emitter_temp_offset_holds",
        "temp_off >= 700 && temp_off <= 1600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "emitter temperature offset +500 in [700, 1600] representing 200-1100 C",
    );
}

#[test]
fn belt_speed_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_speed",
        "speed_x10 >= 1 && speed_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_speed_holds",
        "speed_x10 >= 1 && speed_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt speed x10 m/min in [1, 200]");
}

#[test]
fn wavelength_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wave_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wavelength",
        "wave_x100 >= 50 && wave_x100 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wavelength_holds",
        "wave_x100 >= 50 && wave_x100 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wavelength x100 um in [50, 2000] representing 0.50-20.00 um",
    );
}

#[test]
fn power_density_scaled_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_density",
        "power_x10 >= 10 && power_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_density_holds",
        "power_x10 >= 10 && power_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power density x10 kW/m2 in [10, 500]");
}

#[test]
fn belt_width_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "belt_width",
        "width >= 200 && width <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "belt_width_holds",
        "width >= 200 && width <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt width in [200, 3000] mm");
}

#[test]
fn conveyor_length_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "conveyor_length",
        "length >= 500 && length <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "conveyor_length_holds",
        "length >= 500 && length <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conveyor length in [500, 20000] mm");
}

#[test]
fn emitter_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("emitter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "emitter_type",
        "emitter == 1 || emitter == 2 || emitter == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "emitter_type_holds",
        "emitter == 1 || emitter == 2 || emitter == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "emitter type is ceramic(1) or quartz(2) or metal-sheathed(3)",
    );
}

#[test]
fn atmosphere_control_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "atmosphere",
        "atm == 1 || atm == 2 || atm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "atmosphere_holds",
        "atm == 1 || atm == 2 || atm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "atmosphere control is air(1) or nitrogen(2) or argon(3)",
    );
}

#[test]
fn zone_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zones", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "zone_config",
        "zones == 1 || zones == 2 || zones == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "zone_config_holds",
        "zones == 1 || zones == 2 || zones == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zone config is single(1) or dual(2) or multi(3)");
}

#[test]
fn auto_power_modulation_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_modulation",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_modulation_holds",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto power modulation is off(0) or on(1)");
}
