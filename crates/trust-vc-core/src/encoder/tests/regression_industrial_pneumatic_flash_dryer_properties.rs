// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial pneumatic flash dryer property verification.
// Encodes key parameters of a pneumatic flash dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Duct diameter (mm) — bounded [100, 2000].
/// Value 600 mm.
#[test]
fn test_pneumatic_flash_dryer_duct_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "diameter == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "dia_range",
        "diameter >= 100 && diameter <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "duct diameter 600 mm in [100, 2000]");
}

/// Test 2: Air velocity (m/s) — bounded [10, 40].
/// Value 25 m/s.
#[test]
fn test_pneumatic_flash_dryer_air_velocity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vel_val", "velocity == 25"));
    ctx.push_obligation(ProofObligation::assert(
        "vel_range",
        "velocity >= 10 && velocity <= 40",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air velocity 25 m/s in [10, 40]");
}

/// Test 3: Inlet air temperature offset +100 (deg C) — bounded [200, 800].
/// 200 represents 100 C, 800 represents 700 C. Value 450 (350 C).
#[test]
fn test_pneumatic_flash_dryer_inlet_air_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_off == 450"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_range",
        "temp_off >= 200 && temp_off <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet air temp 350 C (offset 450) in [200, 800]");
}

/// Test 4: Feed rate x10 (0.1 kg/h) — bounded [10, 50000].
/// 10 represents 1.0 kg/h, 50000 represents 5000.0 kg/h. Value 2500 (250.0 kg/h).
#[test]
fn test_pneumatic_flash_dryer_feed_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rate_val", "rate_x10 == 2500"));
    ctx.push_obligation(ProofObligation::assert(
        "rate_range",
        "rate_x10 >= 10 && rate_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 250.0 kg/h (2500 x10) in [10, 50000]");
}

/// Test 5: Residence time x100 (0.01 seconds) — bounded [10, 500].
/// 10 represents 0.10 sec, 500 represents 5.00 sec. Value 50 (0.50 sec).
#[test]
fn test_pneumatic_flash_dryer_residence_time_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume("time_val", "time_x100 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "time_range",
        "time_x100 >= 10 && time_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residence time 0.50 sec (50 x100) in [10, 500]");
}

/// Test 6: Feed system — 3-way disjunction.
/// 1=screw-feeder, 2=venturi, 3=rotary-valve. Value 2 (venturi).
#[test]
fn test_pneumatic_flash_dryer_feed_system_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fs", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fs_val", "fs == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_fs",
        "fs == 1 || fs == 2 || fs == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "feed system 2 (venturi) is valid 3-way disjunction",
    );
}

/// Test 7: Separator type — 3-way disjunction.
/// 1=cyclone, 2=bag-filter, 3=scrubber. Value 1 (cyclone).
#[test]
fn test_pneumatic_flash_dryer_separator_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("st", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st_val", "st == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_st",
        "st == 1 || st == 2 || st == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "separator type 1 (cyclone) is valid 3-way disjunction",
    );
}

/// Test 8: Heating method — 3-way disjunction.
/// 1=direct-gas, 2=indirect-steam, 3=electric. Value 3 (electric).
#[test]
fn test_pneumatic_flash_dryer_heating_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hm_val", "hm == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_hm",
        "hm == 1 || hm == 2 || hm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating method 3 (electric) is valid 3-way disjunction",
    );
}

/// Test 9: Automatic temperature control — boolean flag.
/// 0=disabled, 1=enabled. Value 1 (enabled).
#[test]
fn test_pneumatic_flash_dryer_auto_temperature_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_flag",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto temperature control flag 1 is valid boolean");
}

/// Test 10: Duct length (meters) — bounded [5, 50].
/// Value 20 meters.
#[test]
fn test_pneumatic_flash_dryer_duct_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", i32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "length == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "len_range",
        "length >= 5 && length <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "duct length 20 m in [5, 50]");
}
