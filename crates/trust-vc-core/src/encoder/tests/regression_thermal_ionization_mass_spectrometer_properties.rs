// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates Apache 2.0 License.
//
// Regression tests: thermal ionization mass spectrometer (TIMS) properties.

use super::*;

#[test]
fn test_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("amu", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "amu >= 6 && amu <= 300"));
    ctx.push_obligation(ProofObligation::assume("val", "amu == 238"));
    ctx.push_obligation(ProofObligation::assert("bounded", "amu >= 6 && amu <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range bounded within 6-300 amu");
}

#[test]
fn test_isotope_ratio_precision_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("precision_x10000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "precision_x10000 >= 1 && precision_x10000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "precision_x10000 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "precision_x10000 >= 1 && precision_x10000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "isotope ratio precision x10000 bounded within 1-500 (0.0050 ppm)",
    );
}

#[test]
fn test_filament_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_c", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "temp_c >= 800 && temp_c <= 2500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "temp_c == 1800"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "temp_c >= 800 && temp_c <= 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filament temperature bounded within 800-2500 C");
}

#[test]
fn test_number_of_collectors_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("collectors", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "collectors >= 1 && collectors <= 12",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "collectors == 9"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "collectors >= 1 && collectors <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of collectors bounded within 1-12");
}

#[test]
fn test_accelerating_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("kv", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "kv >= 1 && kv <= 10"));
    ctx.push_obligation(ProofObligation::assume("val", "kv == 8"));
    ctx.push_obligation(ProofObligation::assert("bounded", "kv >= 1 && kv <= 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accelerating voltage bounded within 1-10 kV");
}

#[test]
fn test_filament_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("filament_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "filament_type == 1 || filament_type == 2 || filament_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "filament_type == 1 || filament_type == 2 || filament_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filament type is single, double, or triple");
}

#[test]
fn test_ionization_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ion_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "ion_mode == 1 || ion_mode == 2 || ion_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "ion_mode == 1 || ion_mode == 2 || ion_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ionization mode is positive, negative, or total-evaporation",
    );
}

#[test]
fn test_detector_array_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector array is faraday-only, SEM-only, or mixed-array",
    );
}

#[test]
fn test_ion_lens_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lens_v", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "lens_v >= 100 && lens_v <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "lens_v == 2500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "lens_v >= 100 && lens_v <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ion lens voltage bounded within 100-5000 V");
}

#[test]
fn test_vacuum_interlock_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("interlock_active", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vacuum interlock flag implies conditional evaluates to 1",
    );
}
