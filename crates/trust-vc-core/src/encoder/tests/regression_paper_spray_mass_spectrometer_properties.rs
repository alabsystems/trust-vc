// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Spray voltage (x100 V) — bounded [10, 600].
/// 10 represents 0.10 kV, 600 represents 6.00 kV.
#[test]
fn test_paper_spray_voltage_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_v_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sv_a",
        "spray_v_x100 >= 10 && spray_v_x100 <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sv_c",
        "spray_v_x100 >= 10 && spray_v_x100 <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spray voltage x100 in [10, 600] representing 0.10-6.00 kV",
    );
}

/// Test 2: Solvent volume (uL) — bounded [1, 100].
#[test]
fn test_paper_spray_solvent_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vol_ul", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vol_a",
        "vol_ul >= 1 && vol_ul <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vol_c",
        "vol_ul >= 1 && vol_ul <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "solvent volume in [1, 100] uL");
}

/// Test 3: Paper triangle tip angle (degrees) — bounded [10, 90].
#[test]
fn test_paper_spray_tip_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_deg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ang_a",
        "angle_deg >= 10 && angle_deg <= 90",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ang_c",
        "angle_deg >= 10 && angle_deg <= 90",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "paper tip angle in [10, 90] degrees");
}

/// Test 4: Mass range (m/z) — bounded [50, 2000].
#[test]
fn test_paper_spray_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mz_a", "mz >= 50 && mz <= 2000"));
    ctx.push_obligation(ProofObligation::assert("mz_c", "mz >= 50 && mz <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "paper spray mass range in [50, 2000] m/z");
}

/// Test 5: Paper-to-inlet distance (x10 mm) — bounded [1, 200].
/// 1 represents 0.1 mm, 200 represents 20.0 mm.
#[test]
fn test_paper_spray_inlet_distance_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dist_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dist_a",
        "dist_x10 >= 1 && dist_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dist_c",
        "dist_x10 >= 1 && dist_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "paper-to-inlet distance x10 in [1, 200] representing 0.1-20.0 mm",
    );
}

/// Test 6: Sample spot diameter (x10 mm) — bounded [10, 200].
/// 10 represents 1.0 mm, 200 represents 20.0 mm.
#[test]
fn test_paper_spray_sample_spot_diameter_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spot_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spot_a",
        "spot_x10 >= 10 && spot_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spot_c",
        "spot_x10 >= 10 && spot_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample spot diameter x10 in [10, 200] representing 1.0-20.0 mm",
    );
}

/// Test 7: Paper substrate — 3-way disjunction.
/// 1=chromatography, 2=filter, 3=coated.
#[test]
fn test_paper_spray_substrate_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("substrate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sub_a",
        "substrate == 1 || substrate == 2 || substrate == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sub_c",
        "substrate >= 1 && substrate <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "substrate 3-way (chromatography/filter/coated)");
}

/// Test 8: Solvent system — 3-way disjunction.
/// 1=methanol-water, 2=acetonitrile-water, 3=pure-methanol.
#[test]
fn test_paper_spray_solvent_system_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("solvent", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sol_a",
        "solvent == 1 || solvent == 2 || solvent == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sol_c",
        "solvent >= 1 && solvent <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solvent system 3-way (methanol-water/acetonitrile-water/pure-methanol)",
    );
}

/// Test 9: Ionization polarity — 3-way disjunction.
/// 1=positive, 2=negative, 3=switching.
#[test]
fn test_paper_spray_ionization_polarity_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polarity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pol_a",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pol_c",
        "polarity >= 1 && polarity <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionization polarity 3-way (positive/negative/switching)",
    );
}

/// Test 10: Wetting sensor flag — boolean.
/// 0=disabled, 1=enabled.
#[test]
fn test_paper_spray_wetting_sensor_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wetting sensor flag is boolean (0 or 1)");
}
