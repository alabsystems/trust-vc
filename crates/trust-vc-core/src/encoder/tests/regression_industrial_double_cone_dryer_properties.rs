// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial double cone dryer (tumble dryer) property verification.
// Encodes key parameters of an industrial double cone dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Total volume (x10 L) — scaled volume bounded [10, 200000].
/// 10000 represents 1000.0 L. Value 10000 (1000.0 L total vessel volume).
#[test]
fn test_double_cone_dryer_total_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("total_vol_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vol_val", "total_vol_x10 == 10000"));
    ctx.push_obligation(ProofObligation::assert("vol_min", "total_vol_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "vol_max",
        "total_vol_x10 <= 200000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "total volume 1000.0 L (10000 x10) in [10, 200000]");
}

/// Test 2: Working volume (x10 L) — scaled volume bounded [5, 100000].
/// 6000 represents 600.0 L. Value 6000 (600.0 L working volume).
#[test]
fn test_double_cone_dryer_working_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("work_vol_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("wvol_val", "work_vol_x10 == 6000"));
    ctx.push_obligation(ProofObligation::assert("wvol_min", "work_vol_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert(
        "wvol_max",
        "work_vol_x10 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "working volume 600.0 L (6000 x10) in [5, 100000]");
}

/// Test 3: Rotation speed (x10 RPM) — scaled speed bounded [10, 200].
/// 80 represents 8.0 RPM. Value 80 (8.0 RPM rotation speed).
#[test]
fn test_double_cone_dryer_rotation_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_x10 == 80"));
    ctx.push_obligation(ProofObligation::assert("spd_min", "speed_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("spd_max", "speed_x10 <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed 8.0 RPM (80 x10) in [10, 200]");
}

/// Test 4: Jacket temperature (offset +100 deg C) — bounded [100, 500].
/// 200 represents 100 C. Value 200 (100 C jacket temperature).
#[test]
fn test_double_cone_dryer_jacket_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jacket_temp_off", u32_ty());
    ctx.push_obligation(ProofObligation::assume("jt_val", "jacket_temp_off == 200"));
    ctx.push_obligation(ProofObligation::assert("jt_min", "jacket_temp_off >= 100"));
    ctx.push_obligation(ProofObligation::assert("jt_max", "jacket_temp_off <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jacket temperature 100 C (offset 200) in [100, 500]",
    );
}

/// Test 5: Vacuum level (x10 mbar) — scaled pressure bounded [1, 10000].
/// 50 represents 5.0 mbar. Value 50 (5.0 mbar vacuum level).
#[test]
fn test_double_cone_dryer_vacuum_level_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_val", "vacuum_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert("vac_min", "vacuum_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("vac_max", "vacuum_x10 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum level 5.0 mbar (50 x10) in [1, 10000]");
}

/// Test 6: Cone half-angle (x10 degrees) — scaled angle bounded [200, 600].
/// 450 represents 45.0 degrees. Value 450 (45.0 deg cone half-angle).
#[test]
fn test_double_cone_dryer_cone_half_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ang_val", "angle_x10 == 450"));
    ctx.push_obligation(ProofObligation::assert("ang_min", "angle_x10 >= 200"));
    ctx.push_obligation(ProofObligation::assert("ang_max", "angle_x10 <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cone half-angle 45.0 deg (450 x10) in [200, 600]");
}

/// Test 7: Vessel material — 3-way disjunction.
/// 1=stainless-316L, 2=hastelloy, 3=glass-lined. Value 1 (stainless-316L).
#[test]
fn test_double_cone_dryer_vessel_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vessel_mat", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vm_val", "vessel_mat == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_vessel_mat",
        "vessel_mat == 1 || vessel_mat == 2 || vessel_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vessel material 1 (stainless-316L) is valid 3-way disjunction",
    );
}

/// Test 8: Heating medium — 3-way disjunction.
/// 1=steam, 2=hot-water, 3=thermal-oil. Value 1 (steam).
#[test]
fn test_double_cone_dryer_heating_medium_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_medium", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hm_val", "heat_medium == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_heat_medium",
        "heat_medium == 1 || heat_medium == 2 || heat_medium == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating medium 1 (steam) is valid 3-way disjunction",
    );
}

/// Test 9: Discharge type — 3-way disjunction.
/// 1=butterfly-valve, 2=ball-valve, 3=flush-bottom. Value 1 (butterfly-valve).
#[test]
fn test_double_cone_dryer_discharge_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dt_val", "discharge_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_discharge",
        "discharge_type == 1 || discharge_type == 2 || discharge_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge type 1 (butterfly-valve) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic moisture monitoring — boolean flag using i32 with if/else pattern.
/// Flag 1 = moisture monitoring enabled, monitor_active = 1.
#[test]
fn test_double_cone_dryer_moisture_monitoring_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moisture_flag", i32_ty());
    ctx.declare_var_typed("monitor_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "moisture_flag == 0 || moisture_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "moisture_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "monitor_def",
        "monitor_active == if moisture_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("monitor_on", "monitor_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "moisture monitoring flag activates monitor system");
}
