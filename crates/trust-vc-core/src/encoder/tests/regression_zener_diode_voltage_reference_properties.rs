// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn reference_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vref_mv", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vref_val", "vref_mv == 2500"));
    ctx.push_obligation(ProofObligation::assume(
        "vref_range",
        "vref_mv >= 1200 && vref_mv <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_reference_voltage",
        "vref_mv >= 1200 && vref_mv <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reference voltage 2500mV (2.500V) in range 1200-10000mV",
    );
}

#[test]
fn initial_accuracy() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_ppm", u32_ty());
    ctx.declare_var_typed("accuracy_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("acc_val", "accuracy_ppm == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_ok_def",
        "accuracy_ok == if accuracy_ppm <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_valid",
        "accuracy_ok == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "initial accuracy 50 ppm within max 500 ppm");
}

#[test]
fn temperature_coefficient() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tempco_ppm_per_c", u32_ty());
    ctx.declare_var_typed("tempco_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc_val", "tempco_ppm_per_c == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "tempco_ok_def",
        "tempco_ok == if tempco_ppm_per_c <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tempco_valid", "tempco_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temperature coefficient 5 ppm/C within max 50 ppm/C",
    );
}

#[test]
fn reference_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // 1=buried zener, 2=bandgap, 3=XFET, 4=standard zener
    ctx.push_obligation(ProofObligation::assume("rt_val", "ref_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_type_def",
        "valid_type == if ref_type == 1 || ref_type == 2 || ref_type == 3 || ref_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("type_valid", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reference type 1 (buried zener) is valid 4-way disjunction",
    );
}

#[test]
fn noise_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise_uv", u32_ty());
    ctx.declare_var_typed("noise_ok", i32_ty());
    // Output noise in uV (0.1-10Hz band)
    ctx.push_obligation(ProofObligation::assume("nv_val", "noise_uv == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "noise_ok_def",
        "noise_ok == if noise_uv <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("noise_valid", "noise_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output noise 5 uV (0.1-10Hz) within max 50 uV");
}

#[test]
fn long_term_stability() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drift_ppm_per_kh", u32_ty());
    ctx.declare_var_typed("drift_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lt_val", "drift_ppm_per_kh == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "drift_ok_def",
        "drift_ok == if drift_ppm_per_kh <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("drift_valid", "drift_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "long-term drift 10 ppm/1000h within max 100 ppm/1000h",
    );
}

#[test]
fn load_regulation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("load_reg_ppm_per_ma", u32_ty());
    ctx.declare_var_typed("load_reg_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lr_val",
        "load_reg_ppm_per_ma == 2",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "load_reg_ok_def",
        "load_reg_ok == if load_reg_ppm_per_ma <= 20 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "load_reg_valid",
        "load_reg_ok == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "load regulation 2 ppm/mA within max 20 ppm/mA");
}

#[test]
fn line_regulation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("line_reg_ppm_per_v", u32_ty());
    ctx.declare_var_typed("line_reg_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lrv_val",
        "line_reg_ppm_per_v == 5",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "line_reg_ok_def",
        "line_reg_ok == if line_reg_ppm_per_v <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "line_reg_valid",
        "line_reg_ok == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "line regulation 5 ppm/V within max 50 ppm/V");
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("supply_mv", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sv_val", "supply_mv == 15000"));
    ctx.push_obligation(ProofObligation::assume(
        "supply_range",
        "supply_mv >= 4000 && supply_mv <= 36000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_supply_voltage",
        "supply_mv >= 4000 && supply_mv <= 36000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "supply voltage 15000mV (15V) in range 4000-36000mV",
    );
}

#[test]
fn package_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pkg", u32_ty());
    ctx.declare_var_typed("valid_pkg", i32_ty());
    // 1=TO-92, 2=SOT-23, 3=DIP-8, 4=SOIC-8, 5=ceramic hermetic
    ctx.push_obligation(ProofObligation::assume("pkg_val", "pkg == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_pkg_def",
        "valid_pkg == if pkg == 1 || pkg == 2 || pkg == 3 || pkg == 4 || pkg == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("package_valid", "valid_pkg == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "package type 5 (ceramic hermetic) is valid 5-way disjunction",
    );
}
