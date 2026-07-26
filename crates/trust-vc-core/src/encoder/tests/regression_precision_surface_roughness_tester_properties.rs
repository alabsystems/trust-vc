// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Ra roughness (x10000 um) — bounded [1, 500000].
/// 1 represents 0.0001 um, 500000 represents 50.0000 um.
#[test]
fn test_surface_roughness_ra_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ra_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ra_a",
        "ra_x10000 >= 1 && ra_x10000 <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ra_c",
        "ra_x10000 >= 1 && ra_x10000 <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Ra x10000 in [1, 500000] representing 0.0001-50.0000 um",
    );
}

/// Test 2: Traverse length (x100 mm) — bounded [10, 50000].
/// 10 represents 0.10 mm, 50000 represents 500.00 mm.
#[test]
fn test_surface_roughness_traverse_length_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trav_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tl_a",
        "trav_x100 >= 10 && trav_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tl_c",
        "trav_x100 >= 10 && trav_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "traverse length x100 in [10, 50000] representing 0.10-500.00 mm",
    );
}

/// Test 3: Stylus tip radius (x10 um) — bounded [5, 100].
/// 5 represents 0.5 um, 100 represents 10.0 um.
#[test]
fn test_surface_roughness_stylus_radius_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tip_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tip_a",
        "tip_x10 >= 5 && tip_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tip_c",
        "tip_x10 >= 5 && tip_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "stylus tip radius x10 in [5, 100] representing 0.5-10.0 um",
    );
}

/// Test 4: Traverse speed (x100 mm/s) — bounded [1, 1000].
/// 1 represents 0.01 mm/s, 1000 represents 10.00 mm/s.
#[test]
fn test_surface_roughness_traverse_speed_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ts_a",
        "speed_x100 >= 1 && speed_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ts_c",
        "speed_x100 >= 1 && speed_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "traverse speed x100 in [1, 1000] representing 0.01-10.00 mm/s",
    );
}

/// Test 5: Cutoff wavelength (x100 mm) — bounded [8, 2500].
/// 8 represents 0.08 mm, 2500 represents 25.00 mm.
#[test]
fn test_surface_roughness_cutoff_wavelength_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cutoff_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "co_a",
        "cutoff_x100 >= 8 && cutoff_x100 <= 2500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "co_c",
        "cutoff_x100 >= 8 && cutoff_x100 <= 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cutoff wavelength x100 in [8, 2500] representing 0.08-25.00 mm",
    );
}

/// Test 6: Contact force (x1000 mN) — bounded [1, 10000].
/// 1 represents 0.001 mN, 10000 represents 10.000 mN.
#[test]
fn test_surface_roughness_contact_force_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("force_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cf_a",
        "force_x1000 >= 1 && force_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cf_c",
        "force_x1000 >= 1 && force_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "contact force x1000 in [1, 10000] representing 0.001-10.000 mN",
    );
}

/// Test 7: Measurement method — 3-way disjunction.
/// 1=contact-stylus, 2=optical-confocal, 3=white-light-interferometry.
#[test]
fn test_surface_roughness_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "meth_a",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "meth_c",
        "method >= 1 && method <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "method 3-way (contact-stylus/optical-confocal/white-light-interferometry)",
    );
}

/// Test 8: Surface parameter — 3-way disjunction.
/// 1=Ra, 2=Rz, 3=Rq.
#[test]
fn test_surface_roughness_parameter_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("param", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "par_a",
        "param == 1 || param == 2 || param == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("par_c", "param >= 1 && param <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "surface parameter 3-way (Ra/Rz/Rq)");
}

/// Test 9: Filter type — 3-way disjunction.
/// 1=Gaussian, 2=2RC, 3=spline.
#[test]
fn test_surface_roughness_filter_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("filt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "filt_a",
        "filt == 1 || filt == 2 || filt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("filt_c", "filt >= 1 && filt <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filter type 3-way (Gaussian/2RC/spline)");
}

/// Test 10: Auto-leveling flag — boolean.
/// 0=manual, 1=auto.
#[test]
fn test_surface_roughness_auto_leveling_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-leveling flag is boolean (0 or 1)");
}
