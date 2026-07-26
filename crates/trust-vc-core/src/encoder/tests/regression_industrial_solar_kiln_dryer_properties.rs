// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_solar_kiln_chamber_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chamber_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ct_a",
        "chamber_temp >= 20 && chamber_temp <= 90",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ct_c",
        "chamber_temp >= 20 && chamber_temp <= 90",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "chamber temperature in [20, 90] C for solar-assisted drying",
    );
}

#[test]
fn test_solar_kiln_irradiance_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("irradiance_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ir_a",
        "irradiance_x10 >= 0 && irradiance_x10 <= 12000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ir_c",
        "irradiance_x10 >= 0 && irradiance_x10 <= 12000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "irradiance x10 in [0, 12000] representing 0.0-1200.0 W/m^2",
    );
}

#[test]
fn test_solar_kiln_humidity_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rh_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rh_a",
        "rh_x10 >= 100 && rh_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rh_c",
        "rh_x10 >= 100 && rh_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "relative humidity x10 in [100, 1000] representing 10.0-100.0%",
    );
}

#[test]
fn test_solar_kiln_air_velocity_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_vel_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "av_a",
        "air_vel_x10 >= 5 && air_vel_x10 <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "av_c",
        "air_vel_x10 >= 5 && air_vel_x10 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air velocity x10 in [5, 50] representing 0.5-5.0 m/s",
    );
}

#[test]
fn test_solar_kiln_lumber_moisture_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mc_a",
        "mc_x10 >= 40 && mc_x10 <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mc_c",
        "mc_x10 >= 40 && mc_x10 <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "moisture content x10 in [40, 800] representing 4.0-80.0%",
    );
}

#[test]
fn test_solar_kiln_collector_area_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_m2", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ca_a",
        "area_m2 >= 1 && area_m2 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ca_c",
        "area_m2 >= 1 && area_m2 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "collector area in [1, 500] m^2");
}

#[test]
fn test_solar_kiln_collector_type_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("collector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cl_a",
        "collector == 1 || collector == 2 || collector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cl_c",
        "collector == 1 || collector == 2 || collector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "collector: flat plate, evacuated tube, or parabolic trough",
    );
}

#[test]
fn test_solar_kiln_ventilation_mode_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vent_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vm_a",
        "vent_mode == 1 || vent_mode == 2 || vent_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vm_c",
        "vent_mode == 1 || vent_mode == 2 || vent_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ventilation: natural convection, forced fan, or hybrid",
    );
}

#[test]
fn test_solar_kiln_heat_storage_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("storage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hs_a",
        "storage == 1 || storage == 2 || storage == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hs_c",
        "storage == 1 || storage == 2 || storage == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "storage: rock bed, water tank, or phase-change material",
    );
}

#[test]
fn test_solar_kiln_backup_heater_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("backup", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bh_a",
        "backup == 0 || backup == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bh_c",
        "backup == 0 || backup == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "backup heater flag is boolean");
}
