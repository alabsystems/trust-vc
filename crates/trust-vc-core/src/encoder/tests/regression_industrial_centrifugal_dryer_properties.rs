// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Basket speed (RPM) — bounded [200, 5000].
#[test]
fn test_centrifugal_dryer_basket_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("basket_rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bs_a",
        "basket_rpm >= 200 && basket_rpm <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bs_c",
        "basket_rpm >= 200 && basket_rpm <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "basket speed in [200, 5000] RPM");
}

/// Test 2: Hot air temperature offset +100 (deg C) — bounded [150, 450].
/// 150 represents 50 C, 450 represents 350 C.
#[test]
fn test_centrifugal_dryer_air_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_a",
        "air_temp >= 150 && air_temp <= 450",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_c",
        "air_temp >= 150 && air_temp <= 450",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air temp offset+100 in [150, 450] representing 50-350 C",
    );
}

/// Test 3: G-force (x10) — bounded [100, 30000].
/// 100 represents 10.0 G, 30000 represents 3000.0 G.
#[test]
fn test_centrifugal_dryer_g_force_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gforce_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gf_a",
        "gforce_x10 >= 100 && gforce_x10 <= 30000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gf_c",
        "gforce_x10 >= 100 && gforce_x10 <= 30000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "G-force x10 in [100, 30000] representing 10.0-3000.0 G",
    );
}

/// Test 4: Spin cycle time (seconds) — bounded [10, 3600].
#[test]
fn test_centrifugal_dryer_spin_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spin_s", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "spin_s >= 10 && spin_s <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "spin_s >= 10 && spin_s <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spin cycle time in [10, 3600] seconds");
}

/// Test 5: Airflow rate (x10 m3/min) — bounded [1, 5000].
/// 1 represents 0.1 m3/min, 5000 represents 500.0 m3/min.
#[test]
fn test_centrifugal_dryer_airflow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("airflow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "af_a",
        "airflow_x10 >= 1 && airflow_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "af_c",
        "airflow_x10 >= 1 && airflow_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "airflow rate x10 in [1, 5000] representing 0.1-500.0 m3/min",
    );
}

/// Test 6: Residual moisture (x100 %) — bounded [10, 5000].
/// 10 represents 0.10%, 5000 represents 50.00%.
#[test]
fn test_centrifugal_dryer_residual_moisture_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moist_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rm_a",
        "moist_x100 >= 10 && moist_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rm_c",
        "moist_x100 >= 10 && moist_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "residual moisture x100 in [10, 5000] representing 0.10-50.00%",
    );
}

/// Test 7: Basket type — 3-way disjunction.
/// 1=perforated, 2=solid-bowl, 3=conical-screen.
#[test]
fn test_centrifugal_dryer_basket_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("basket", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bk_a",
        "basket == 1 || basket == 2 || basket == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bk_c",
        "basket >= 1 && basket <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "basket type 3-way (perforated/solid-bowl/conical-screen)",
    );
}

/// Test 8: Discharge method — 3-way disjunction.
/// 1=manual-unload, 2=bottom-plow, 3=inverting-bag.
#[test]
fn test_centrifugal_dryer_discharge_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dm_a",
        "discharge == 1 || discharge == 2 || discharge == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dm_c",
        "discharge >= 1 && discharge <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge method 3-way (manual/bottom-plow/inverting-bag)",
    );
}

/// Test 9: Drive type — 3-way disjunction.
/// 1=direct, 2=belt, 3=gear.
#[test]
fn test_centrifugal_dryer_drive_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drv_a",
        "drive == 1 || drive == 2 || drive == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("drv_c", "drive >= 1 && drive <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive type 3-way (direct/belt/gear)");
}

/// Test 10: Inert gas purge flag — boolean.
/// 0=disabled, 1=enabled.
#[test]
fn test_centrifugal_dryer_inert_gas_purge_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inert gas purge flag is boolean (0 or 1)");
}
