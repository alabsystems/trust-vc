// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial tunnel kiln dryer property verification.
// Encodes key parameters of a tunnel kiln dryer (ceramic, brick, refractory firing)
// and verifies bounded, offset, scaled, disjunctive, and boolean-flag constraints.

/// Test 1: Kiln length (m) — bounded [5, 200], value 120.
#[test]
fn test_tunnel_kiln_dryer_kiln_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("kiln_len", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "kiln_len == 120"));
    ctx.push_obligation(ProofObligation::assert("len_min", "kiln_len >= 5"));
    ctx.push_obligation(ProofObligation::assert("len_max", "kiln_len <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "kiln length 120 m in [5, 200]");
}

/// Test 2: Max temperature (offset +100 deg C) — assume temp_off > 100 && temp_off < 2000,
/// assert within range. Actual temp = temp_off - 100, so temp_off of 1450 = 1350 C.
#[test]
fn test_tunnel_kiln_dryer_max_temperature_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off > 100 && temp_off < 2000",
    ));
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_off == 1450"));
    ctx.push_obligation(ProofObligation::assert("temp_above", "temp_off > 100"));
    ctx.push_obligation(ProofObligation::assert("temp_below", "temp_off < 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "max temperature offset 1450 (1350 C) in (100, 2000)",
    );
}

/// Test 3: Throughput (x10 tonnes/h) — scaled at 0.1 tonnes/h, bounded (0, 10000).
/// Value 250 represents 25.0 tonnes/h.
#[test]
fn test_tunnel_kiln_dryer_throughput_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "rate_x10 > 0 && rate_x10 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("rate_val", "rate_x10 == 250"));
    ctx.push_obligation(ProofObligation::assert("rate_pos", "rate_x10 > 0"));
    ctx.push_obligation(ProofObligation::assert("rate_cap", "rate_x10 < 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 25.0 tonnes/h (250 x10) in (0, 10000)");
}

/// Test 4: Cross section width (x10 mm) — scaled at 0.1 mm, bounded (0, 100000).
/// Value 30000 represents 3000.0 mm = 3.0 m.
#[test]
fn test_tunnel_kiln_dryer_cross_section_width_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "width_range",
        "width_x10 > 0 && width_x10 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("width_val", "width_x10 == 30000"));
    ctx.push_obligation(ProofObligation::assert("width_pos", "width_x10 > 0"));
    ctx.push_obligation(ProofObligation::assert("width_cap", "width_x10 < 100000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cross section width 3000.0 mm (30000 x10) in (0, 100000)",
    );
}

/// Test 5: Residence time (x10 hours) — scaled at 0.1 hours, bounded (0, 10000).
/// Value 480 represents 48.0 hours.
#[test]
fn test_tunnel_kiln_dryer_residence_time_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_range",
        "time_x10 > 0 && time_x10 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("time_val", "time_x10 == 480"));
    ctx.push_obligation(ProofObligation::assert("time_pos", "time_x10 > 0"));
    ctx.push_obligation(ProofObligation::assert("time_cap", "time_x10 < 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residence time 48.0 hours (480 x10) in (0, 10000)");
}

/// Test 6: Number of temperature zones — bounded [1, 20], value 8.
#[test]
fn test_tunnel_kiln_dryer_temperature_zones_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_zones", u32_ty());
    ctx.push_obligation(ProofObligation::assume("zones_val", "num_zones == 8"));
    ctx.push_obligation(ProofObligation::assert("zones_min", "num_zones >= 1"));
    ctx.push_obligation(ProofObligation::assert("zones_max", "num_zones <= 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of temperature zones 8 in [1, 20]");
}

/// Test 7: Fuel type — 3-way disjunction.
/// 1=natural-gas, 2=heavy-oil, 3=coal. Value 1 (natural-gas).
#[test]
fn test_tunnel_kiln_dryer_fuel_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fuel", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fuel_val", "fuel == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_fuel",
        "fuel == 1 || fuel == 2 || fuel == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fuel type 1 (natural-gas) is valid 3-way disjunction",
    );
}

/// Test 8: Car transport mechanism — 3-way disjunction.
/// 1=roller, 2=pusher, 3=walking-beam. Value 2 (pusher).
#[test]
fn test_tunnel_kiln_dryer_car_transport_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("car", u32_ty());
    ctx.push_obligation(ProofObligation::assume("car_val", "car == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_car",
        "car == 1 || car == 2 || car == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "car transport 2 (pusher) is valid 3-way disjunction",
    );
}

/// Test 9: Firing mode — 3-way disjunction.
/// 1=direct, 2=indirect, 3=muffle. Value 3 (muffle).
#[test]
fn test_tunnel_kiln_dryer_firing_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_mode",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "firing mode 3 (muffle) is valid 3-way disjunction");
}

/// Test 10: Automatic zone temperature control — boolean flag using i32 with if/else.
/// Flag 1 = automatic control enabled, control_active = 1.
#[test]
fn test_tunnel_kiln_dryer_auto_zone_temp_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_flag", i32_ty());
    ctx.declare_var_typed("control_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "auto_flag == 0 || auto_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "auto_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "control_def",
        "control_active == if auto_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("control_on", "control_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic zone temperature control flag activates control",
    );
}
