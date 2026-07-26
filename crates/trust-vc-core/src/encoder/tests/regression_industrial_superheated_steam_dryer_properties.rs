// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial superheated steam dryer property verification.
// Encodes key parameters of a superheated steam dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Steam temperature (offset +100 deg C, so 300 deg C = 400) — bounded [200, 800].
/// Value 400 represents 300 deg C actual temperature.
#[test]
fn test_steam_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("steam_temp_offset", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_val",
        "steam_temp_offset == 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_min",
        "steam_temp_offset >= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_max",
        "steam_temp_offset <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "steam temperature 300 C (400 offset) in [200, 800]",
    );
}

/// Test 2: Steam pressure (x10 bar, so 30 = 3.0 bar) — bounded [1, 100].
/// Value 30 represents 3.0 bar.
#[test]
fn test_steam_pressure_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sp_val", "pressure_x10 == 30"));
    ctx.push_obligation(ProofObligation::assert("sp_min", "pressure_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("sp_max", "pressure_x10 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "steam pressure 3.0 bar (30 x10) in [1, 100]");
}

/// Test 3: Steam velocity (x10 m/s, so 100 = 10.0 m/s) — bounded [10, 500].
/// Value 100 represents 10.0 m/s.
#[test]
fn test_steam_velocity_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sv_val", "velocity_x10 == 100"));
    ctx.push_obligation(ProofObligation::assert("sv_min", "velocity_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("sv_max", "velocity_x10 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "steam velocity 10.0 m/s (100 x10) in [10, 500]");
}

/// Test 4: Throughput (x10 kg/h, so 5000 = 500.0 kg/h) — bounded [10, 100000].
/// Value 5000 represents 500.0 kg/h.
#[test]
fn test_throughput_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("thr_val", "throughput_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert("thr_min", "throughput_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "thr_max",
        "throughput_x10 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 500.0 kg/h (5000 x10) in [10, 100000]");
}

/// Test 5: Residence time (x10 min, so 50 = 5.0 min) — bounded [1, 600].
/// Value 50 represents 5.0 minutes.
#[test]
fn test_residence_time_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("residence_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rt_val", "residence_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert("rt_min", "residence_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("rt_max", "residence_x10 <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residence time 5.0 min (50 x10) in [1, 600]");
}

/// Test 6: Number of stages — bounded [1, 10], value 3.
#[test]
fn test_number_of_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_stages", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ns_val", "num_stages == 3"));
    ctx.push_obligation(ProofObligation::assert("ns_min", "num_stages >= 1"));
    ctx.push_obligation(ProofObligation::assert("ns_max", "num_stages <= 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of stages 3 in [1, 10]");
}

/// Test 7: Dryer geometry — 3-way disjunction.
/// 1=flash, 2=fluidized-bed, 3=impinging-jet. Value 1 (flash).
#[test]
fn test_dryer_geometry_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dryer_geom", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dg_val", "dryer_geom == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_dryer_geom",
        "dryer_geom == 1 || dryer_geom == 2 || dryer_geom == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dryer geometry 1 (flash) is valid 3-way disjunction",
    );
}

/// Test 8: Steam recirculation — 3-way disjunction.
/// 1=open-loop, 2=closed-loop, 3=partial-recycle. Value 2 (closed-loop).
#[test]
fn test_steam_recirculation_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("steam_recirc", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sr_val", "steam_recirc == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_steam_recirc",
        "steam_recirc == 1 || steam_recirc == 2 || steam_recirc == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "steam recirculation 2 (closed-loop) is valid 3-way disjunction",
    );
}

/// Test 9: Product discharge — 3-way disjunction.
/// 1=cyclone, 2=bag-filter, 3=rotary-valve. Value 1 (cyclone).
#[test]
fn test_product_discharge_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prod_discharge", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pd_val", "prod_discharge == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_prod_discharge",
        "prod_discharge == 1 || prod_discharge == 2 || prod_discharge == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "product discharge 1 (cyclone) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic superheat control — boolean flag using i32 with if/else pattern.
/// Flag 1 = superheat control enabled, control_active = 1.
#[test]
fn test_automatic_superheat_control_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("superheat_flag", i32_ty());
    ctx.declare_var_typed("control_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "superheat_flag == 0 || superheat_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "superheat_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "control_def",
        "control_active == if superheat_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("control_on", "control_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "superheat control flag activates automatic control",
    );
}
