// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Orbital radius (x100 mm) — bounded [10, 2000].
/// 10 represents 0.10 mm, 2000 represents 20.00 mm.
#[test]
fn test_scroll_orbital_radius_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("radius_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rad_a",
        "radius_x100 >= 10 && radius_x100 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rad_c",
        "radius_x100 >= 10 && radius_x100 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "orbital radius x100 in [10, 2000] representing 0.10-20.00 mm",
    );
}

/// Test 2: Orbiting speed (RPM) — bounded [500, 12000].
#[test]
fn test_scroll_orbital_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spd_a",
        "speed_rpm >= 500 && speed_rpm <= 12000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spd_c",
        "speed_rpm >= 500 && speed_rpm <= 12000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "orbiting speed in [500, 12000] RPM");
}

/// Test 3: Discharge pressure (x10 bar) — bounded [20, 4000].
/// 20 represents 2.0 bar, 4000 represents 400.0 bar.
#[test]
fn test_scroll_orbital_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "disc_x10 >= 20 && disc_x10 <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "disc_x10 >= 20 && disc_x10 <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 in [20, 4000] representing 2.0-400.0 bar",
    );
}

/// Test 4: Scroll wrap height (x100 mm) — bounded [100, 10000].
/// 100 represents 1.00 mm, 10000 represents 100.00 mm.
#[test]
fn test_scroll_orbital_wrap_height_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("height_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ht_a",
        "height_x100 >= 100 && height_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ht_c",
        "height_x100 >= 100 && height_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wrap height x100 in [100, 10000] representing 1.00-100.00 mm",
    );
}

/// Test 5: Motor current (x100 A) — bounded [10, 20000].
/// 10 represents 0.10 A, 20000 represents 200.00 A.
#[test]
fn test_scroll_orbital_motor_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curr_a",
        "curr_x100 >= 10 && curr_x100 <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "curr_c",
        "curr_x100 >= 10 && curr_x100 <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motor current x100 in [10, 20000] representing 0.10-200.00 A",
    );
}

/// Test 6: Volumetric efficiency (x100 %) — bounded [5000, 9800].
/// 5000 represents 50.00%, 9800 represents 98.00%.
#[test]
fn test_scroll_orbital_volumetric_efficiency_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vol_eff", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ve_a",
        "vol_eff >= 5000 && vol_eff <= 9800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ve_c",
        "vol_eff >= 5000 && vol_eff <= 9800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "volumetric efficiency x100 in [5000, 9800] representing 50.00-98.00%",
    );
}

/// Test 7: Tip seal material — 3-way disjunction.
/// 1=PTFE, 2=PEEK, 3=carbon-graphite.
#[test]
fn test_scroll_orbital_tip_seal_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "seal_a",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("seal_c", "seal >= 1 && seal <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tip seal material 3-way (PTFE/PEEK/carbon-graphite)",
    );
}

/// Test 8: Lubrication method — 3-way disjunction.
/// 1=oil-free, 2=oil-injected, 3=grease-packed.
#[test]
fn test_scroll_orbital_lubrication_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lube", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lube_a",
        "lube == 1 || lube == 2 || lube == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("lube_c", "lube >= 1 && lube <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lubrication 3-way (oil-free/oil-injected/grease-packed)",
    );
}

/// Test 9: Scroll wrap profile — 3-way disjunction.
/// 1=involute, 2=algebraic, 3=hybrid.
#[test]
fn test_scroll_orbital_wrap_profile_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("profile", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "prof_a",
        "profile == 1 || profile == 2 || profile == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "prof_c",
        "profile >= 1 && profile <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wrap profile 3-way (involute/algebraic/hybrid)");
}

/// Test 10: Variable speed drive flag — boolean.
/// 0=fixed, 1=variable.
#[test]
fn test_scroll_orbital_variable_speed_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "variable speed drive flag is boolean (0 or 1)");
}
