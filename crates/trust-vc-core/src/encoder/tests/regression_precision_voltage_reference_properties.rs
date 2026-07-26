// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_output_voltage_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volt_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "volt_range",
        "volt_x1000 >= 1000 && volt_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("volt_val", "volt_x1000 == 7000"));
    ctx.push_obligation(ProofObligation::assert(
        "output_voltage",
        "volt_x1000 == 7000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "7.000V output (7000 mV scaled x1000) within 1.000-10.000V range",
    );
}

#[test]
fn test_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_range",
        "acc_x10000 >= 1 && acc_x10000 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("acc_val", "acc_x10000 == 5"));
    ctx.push_obligation(ProofObligation::assert("accuracy", "acc_x10000 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "0.0005% accuracy (5 scaled x10000) within 0.0001-0.0100% range",
    );
}

#[test]
fn test_temp_coefficient_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tc_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tc_range",
        "tc_x10 >= 1 && tc_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("tc_val", "tc_x10 == 25"));
    ctx.push_obligation(ProofObligation::assert("temp_coefficient", "tc_x10 == 25"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "2.5 ppm/C tempco (25 scaled x10) within 0.1-10.0 ppm/C range",
    );
}

#[test]
fn test_long_term_stability_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stab_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stab_range",
        "stab_x100 >= 1 && stab_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("stab_val", "stab_x100 == 50"));
    ctx.push_obligation(ProofObligation::assert("stability", "stab_x100 == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "0.50 ppm/yr drift (50 scaled x100) within 0.01-5.00 ppm/yr range",
    );
}

#[test]
fn test_noise_voltage_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "noise_range",
        "noise_x10 >= 1 && noise_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("noise_val", "noise_x10 == 30"));
    ctx.push_obligation(ProofObligation::assert("noise_voltage", "noise_x10 == 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "3.0 uVpp noise (30 scaled x10) within 0.1-20.0 uVpp range",
    );
}

#[test]
fn test_output_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curr_range",
        "curr >= 1 && curr <= 50",
    ));
    ctx.push_obligation(ProofObligation::assume("curr_val", "curr == 25"));
    ctx.push_obligation(ProofObligation::assert("output_current", "curr == 25"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "25 mA max output current within 1-50 mA range");
}

#[test]
fn test_reference_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_type", u8_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_type",
        "ref_type == 1 || ref_type == 2 || ref_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "type_bounded",
        "ref_type >= 1 && ref_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reference type (1=zener, 2=bandgap, 3=buried-zener) implies [1,3]",
    );
}

#[test]
fn test_package_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pkg_type", u8_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_pkg",
        "pkg_type == 1 || pkg_type == 2 || pkg_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pkg_bounded",
        "pkg_type >= 1 && pkg_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "package type (1=TO-99, 2=DIP-8, 3=SOIC-8) implies [1,3]",
    );
}

#[test]
fn test_temperature_grade_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("grade", u8_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_grade",
        "grade == 1 || grade == 2 || grade == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "grade_bounded",
        "grade >= 1 && grade <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temperature grade (1=commercial, 2=industrial, 3=military) implies [1,3]",
    );
}

#[test]
fn test_hermetic_sealed_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume("seal_set", "seal == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "flag_is_true",
        "if seal == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hermetic sealed flag set to 1 evaluates to true");
}
