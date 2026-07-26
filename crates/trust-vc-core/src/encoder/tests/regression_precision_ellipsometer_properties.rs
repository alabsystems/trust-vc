// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ellipsometer_psi_angle_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("psi_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "psi_a",
        "psi_x100 >= 0 && psi_x100 <= 9000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "psi_c",
        "psi_x100 >= 0 && psi_x100 <= 9000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "psi angle x100 in [0, 9000] representing 0.00-90.00 degrees",
    );
}

#[test]
fn test_ellipsometer_delta_angle_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("delta_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "del_a",
        "delta_x100 >= 0 && delta_x100 <= 36000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "del_c",
        "delta_x100 >= 0 && delta_x100 <= 36000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "delta angle x100 in [0, 36000] representing 0.00-360.00 degrees",
    );
}

#[test]
fn test_ellipsometer_wavelength_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wl_a",
        "wavelength_nm >= 190 && wavelength_nm <= 2500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wl_c",
        "wavelength_nm >= 190 && wavelength_nm <= 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength in [190, 2500] nm");
}

#[test]
fn test_ellipsometer_angle_of_incidence_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("aoi_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "aoi_a",
        "aoi_x10 >= 200 && aoi_x10 <= 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aoi_c",
        "aoi_x10 >= 200 && aoi_x10 <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "angle of incidence x10 in [200, 900] representing 20.0-90.0 degrees",
    );
}

#[test]
fn test_ellipsometer_film_thickness_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thick_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ft_a",
        "thick_x10 >= 1 && thick_x10 <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ft_c",
        "thick_x10 >= 1 && thick_x10 <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "film thickness x10 in [1, 1000000] representing 0.1-100000.0 Angstroms",
    );
}

#[test]
fn test_ellipsometer_refractive_index_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ri_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ri_a",
        "ri_x10000 >= 10000 && ri_x10000 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ri_c",
        "ri_x10000 >= 10000 && ri_x10000 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "refractive index x10000 in [10000, 50000] representing 1.0000-5.0000",
    );
}

#[test]
fn test_ellipsometer_light_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ls_a",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ls_c",
        "source >= 1 && source <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "light source 3-way (HeNe-laser/xenon-lamp/LED)");
}

#[test]
fn test_ellipsometer_polarizer_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polarizer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pol_a",
        "polarizer == 1 || polarizer == 2 || polarizer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pol_c",
        "polarizer >= 1 && polarizer <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "polarizer type 3-way (rotating-analyzer/rotating-compensator/phase-modulated)",
    );
}

#[test]
fn test_ellipsometer_measurement_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mm_a",
        "meas_mode == 1 || meas_mode == 2 || meas_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mm_c",
        "meas_mode >= 1 && meas_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement mode 3-way (single-wavelength/spectroscopic/imaging)",
    );
}

#[test]
fn test_ellipsometer_in_situ_monitoring_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "in-situ monitoring flag is boolean (0 or 1)");
}
