// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Drum surface temperature offset +100 (deg C) — bounded [200, 500].
/// 200 represents 100 C, 500 represents 400 C.
#[test]
fn test_contact_drum_surface_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drum_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "drum_temp >= 200 && drum_temp <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "drum_temp >= 200 && drum_temp <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drum surface temp offset+100 in [200, 500] representing 100-400 C",
    );
}

/// Test 2: Drum rotation speed (x100 RPM) — bounded [1, 5000].
/// 1 represents 0.01 RPM, 5000 represents 50.00 RPM.
#[test]
fn test_contact_drum_rotation_speed_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_a",
        "rpm_x100 >= 1 && rpm_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_c",
        "rpm_x100 >= 1 && rpm_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drum rotation x100 in [1, 5000] representing 0.01-50.00 RPM",
    );
}

/// Test 3: Film thickness (x10 mm) — bounded [1, 100].
/// 1 represents 0.1 mm, 100 represents 10.0 mm.
#[test]
fn test_contact_drum_film_thickness_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("film_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "film_a",
        "film_x10 >= 1 && film_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "film_c",
        "film_x10 >= 1 && film_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "film thickness x10 in [1, 100] representing 0.1-10.0 mm",
    );
}

/// Test 4: Steam pressure (x10 bar) — bounded [10, 100].
/// 10 represents 1.0 bar, 100 represents 10.0 bar.
#[test]
fn test_contact_drum_steam_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("steam_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sp_a",
        "steam_x10 >= 10 && steam_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sp_c",
        "steam_x10 >= 10 && steam_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "steam pressure x10 in [10, 100] representing 1.0-10.0 bar",
    );
}

/// Test 5: Knife gap (x100 mm) — bounded [1, 500].
/// 1 represents 0.01 mm, 500 represents 5.00 mm.
#[test]
fn test_contact_drum_knife_gap_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gap_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gap_a",
        "gap_x100 >= 1 && gap_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gap_c",
        "gap_x100 >= 1 && gap_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "knife gap x100 in [1, 500] representing 0.01-5.00 mm",
    );
}

/// Test 6: Product moisture target (x100 %) — bounded [100, 9000].
/// 100 represents 1.00%, 9000 represents 90.00%.
#[test]
fn test_contact_drum_moisture_target_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moist_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "moist_a",
        "moist_x100 >= 100 && moist_x100 <= 9000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "moist_c",
        "moist_x100 >= 100 && moist_x100 <= 9000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "moisture target x100 in [100, 9000] representing 1.00-90.00%",
    );
}

/// Test 7: Drum configuration — 3-way disjunction.
/// 1=single-drum, 2=double-drum, 3=twin-drum.
#[test]
fn test_contact_drum_configuration_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("config", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cfg_a",
        "config == 1 || config == 2 || config == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cfg_c",
        "config >= 1 && config <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drum config 3-way (single/double/twin)");
}

/// Test 8: Feed method — 3-way disjunction.
/// 1=dip, 2=spray, 3=applicator-roll.
#[test]
fn test_contact_drum_feed_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "feed_a",
        "feed == 1 || feed == 2 || feed == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("feed_c", "feed >= 1 && feed <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed method 3-way (dip/spray/applicator-roll)");
}

/// Test 9: Heating source — 3-way disjunction.
/// 1=steam, 2=hot-water, 3=thermal-oil.
#[test]
fn test_contact_drum_heating_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heat_a",
        "heat == 1 || heat == 2 || heat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("heat_c", "heat >= 1 && heat <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating source 3-way (steam/hot-water/thermal-oil)",
    );
}

/// Test 10: Vacuum operation flag — boolean.
/// 0=atmospheric, 1=vacuum.
#[test]
fn test_contact_drum_vacuum_operation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum operation flag is boolean (0 or 1)");
}
