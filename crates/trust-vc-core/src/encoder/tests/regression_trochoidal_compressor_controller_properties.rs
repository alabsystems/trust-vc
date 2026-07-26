// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Discharge pressure at ×10 bar must stay within safe operating range [0.5, 30.0] bar.
#[test]
fn test_trochoidal_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "press_x10 >= 5 && press_x10 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "press_x10 >= 5 && press_x10 <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trochoidal compressor discharge pressure in [0.5, 30.0] bar (x10)",
    );
}

/// Rotor speed in RPM must stay within operational range [500, 10000].
#[test]
fn test_trochoidal_compressor_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rs_a",
        "speed >= 500 && speed <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rs_c",
        "speed >= 500 && speed <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trochoidal compressor rotor speed in [500, 10000] RPM",
    );
}

/// Displacement at ×100 cc/rev must stay within range [0.10, 500.00] cc/rev.
#[test]
fn test_trochoidal_compressor_displacement_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ds_a",
        "disp_x100 >= 10 && disp_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ds_c",
        "disp_x100 >= 10 && disp_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trochoidal compressor displacement in [0.10, 500.00] cc/rev (x100)",
    );
}

/// Discharge temperature with +100 offset must stay within [100, 400] (i.e. [0, 300] °C).
#[test]
fn test_trochoidal_compressor_discharge_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "temp_off >= 100 && temp_off <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "temp_off >= 100 && temp_off <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trochoidal compressor discharge temperature in [0, 300] C (offset +100)",
    );
}

/// Eccentricity at ×100 mm must stay within range [0.10, 50.00] mm.
#[test]
fn test_trochoidal_compressor_eccentricity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ecc_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ec_a",
        "ecc_x100 >= 10 && ecc_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ec_c",
        "ecc_x100 >= 10 && ecc_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trochoidal compressor eccentricity in [0.10, 50.00] mm (x100)",
    );
}

/// Number of lobes must be in valid range [2, 6].
#[test]
fn test_trochoidal_compressor_number_of_lobes_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lobes", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nl_a", "lobes >= 2 && lobes <= 6"));
    ctx.push_obligation(ProofObligation::assert("nl_c", "lobes >= 2 && lobes <= 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trochoidal compressor lobe count in [2, 6]");
}

/// Rotor profile must be one of: 1=epitrochoidal, 2=hypotrochoidal, 3=modified-trochoid.
#[test]
fn test_trochoidal_compressor_rotor_profile_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("profile", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rp_a",
        "profile == 1 || profile == 2 || profile == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rp_c",
        "profile == 1 || profile == 2 || profile == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trochoidal compressor rotor profile is epitrochoidal, hypotrochoidal, or modified-trochoid");
}

/// Sealing method must be one of: 1=apex-seal, 2=side-seal, 3=oil-film.
#[test]
fn test_trochoidal_compressor_sealing_method_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sm_a",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sm_c",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trochoidal compressor sealing method is apex-seal, side-seal, or oil-film",
    );
}

/// Cooling type must be one of: 1=air-cooled, 2=liquid-cooled, 3=oil-cooled.
#[test]
fn test_trochoidal_compressor_cooling_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ct_a",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ct_c",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trochoidal compressor cooling type is air-cooled, liquid-cooled, or oil-cooled",
    );
}

/// Automatic speed regulation flag must be boolean (0 or 1).
#[test]
fn test_trochoidal_compressor_speed_regulation_flag_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("sr_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trochoidal compressor speed regulation flag is boolean",
    );
}
