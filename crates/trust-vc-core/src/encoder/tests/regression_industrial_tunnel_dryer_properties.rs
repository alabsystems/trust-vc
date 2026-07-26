// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial tunnel dryer property verification.
// Encodes key parameters of an industrial tunnel dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Tunnel length (m) — bounded [5, 100], value 30.
#[test]
fn test_tunnel_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tunnel_length", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "tunnel_length == 30"));
    ctx.push_obligation(ProofObligation::assert("len_min", "tunnel_length >= 5"));
    ctx.push_obligation(ProofObligation::assert("len_max", "tunnel_length <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tunnel length 30 m in [5, 100]");
}

/// Test 2: Conveyor speed (x10 m/min) — scaled at 0.1 m/min, bounded [1, 500].
/// 1 represents 0.1 m/min, 500 represents 50.0 m/min. Value 25 (2.5 m/min).
#[test]
fn test_conveyor_speed_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_x10 == 25"));
    ctx.push_obligation(ProofObligation::assert("spd_min", "speed_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("spd_max", "speed_x10 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conveyor speed 2.5 m/min (25 x10) in [1, 500]");
}

/// Test 3: Drying temperature (deg C) — bounded [40, 250], value 120.
#[test]
fn test_drying_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dry_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "dry_temp == 120"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "dry_temp >= 40"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "dry_temp <= 250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drying temperature 120 C in [40, 250]");
}

/// Test 4: Air velocity (x10 m/s) — scaled at 0.1 m/s, bounded [5, 100].
/// 5 represents 0.5 m/s, 100 represents 10.0 m/s. Value 30 (3.0 m/s).
#[test]
fn test_air_velocity_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vel_val", "velocity_x10 == 30"));
    ctx.push_obligation(ProofObligation::assert("vel_min", "velocity_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("vel_max", "velocity_x10 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air velocity 3.0 m/s (30 x10) in [5, 100]");
}

/// Test 5: Throughput (kg/h) — bounded [50, 10000], value 2000.
#[test]
fn test_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput", u32_ty());
    ctx.push_obligation(ProofObligation::assume("thr_val", "throughput == 2000"));
    ctx.push_obligation(ProofObligation::assert("thr_min", "throughput >= 50"));
    ctx.push_obligation(ProofObligation::assert("thr_max", "throughput <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 2000 kg/h in [50, 10000]");
}

/// Test 6: Air flow direction — 3-way disjunction.
/// 1=co-current, 2=counter-current, 3=cross-flow. Value 2 (counter-current).
#[test]
fn test_air_flow_direction_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_dir", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fd_val", "flow_dir == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_flow_dir",
        "flow_dir == 1 || flow_dir == 2 || flow_dir == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air flow direction 2 (counter-current) is valid 3-way disjunction",
    );
}

/// Test 7: Heating source — 3-way disjunction.
/// 1=gas-burner, 2=steam-coil, 3=infrared. Value 1 (gas-burner).
#[test]
fn test_heating_source_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_src", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hs_val", "heat_src == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_heat_src",
        "heat_src == 1 || heat_src == 2 || heat_src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating source 1 (gas-burner) is valid 3-way disjunction",
    );
}

/// Test 8: Conveyor type — 3-way disjunction.
/// 1=belt, 2=tray-cart, 3=roller. Value 3 (roller).
#[test]
fn test_conveyor_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conv_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ct_val", "conv_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_conv_type",
        "conv_type == 1 || conv_type == 2 || conv_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "conveyor type 3 (roller) is valid 3-way disjunction",
    );
}

/// Test 9: Number of zones — bounded [1, 12], value 6.
#[test]
fn test_number_of_zones_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_zones", u32_ty());
    ctx.push_obligation(ProofObligation::assume("zones_val", "num_zones == 6"));
    ctx.push_obligation(ProofObligation::assert("zones_min", "num_zones >= 1"));
    ctx.push_obligation(ProofObligation::assert("zones_max", "num_zones <= 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of zones 6 in [1, 12]");
}

/// Test 10: Heat recovery — boolean flag using i32 with if/else pattern.
/// Flag 1 = heat recovery system installed, recovery_active = 1.
#[test]
fn test_heat_recovery_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("recovery_flag", i32_ty());
    ctx.declare_var_typed("recovery_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "recovery_flag == 0 || recovery_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "recovery_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "recovery_def",
        "recovery_active == if recovery_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "recovery_on",
        "recovery_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heat recovery flag activates recovery system");
}
