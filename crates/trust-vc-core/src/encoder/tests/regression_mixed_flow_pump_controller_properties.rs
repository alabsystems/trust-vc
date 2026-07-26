// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_mixed_pump_impeller_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dia", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dia_bounds",
        "dia >= 150 && dia <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dia_check",
        "dia >= 150 && dia <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller diameter 150-1500mm bounded");
}

#[test]
fn test_mixed_pump_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_bounds",
        "flow >= 500 && flow <= 200000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_check",
        "flow >= 500 && flow <= 200000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 500-200000 L/min bounded");
}

#[test]
fn test_mixed_pump_head_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "head_bounds",
        "head_x10 >= 20 && head_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "head_check",
        "head_x10 >= 20 && head_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "head x10 meters 20-500 (2.0-50.0m) bounded");
}

#[test]
fn test_mixed_pump_efficiency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eff_bounds",
        "eff_x10 >= 600 && eff_x10 <= 920",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eff_check",
        "eff_x10 >= 600 && eff_x10 <= 920",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "efficiency x10 percent 600-920 (60.0-92.0%) bounded",
    );
}

#[test]
fn test_mixed_pump_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_bounds",
        "rpm >= 200 && rpm <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_check",
        "rpm >= 200 && rpm <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotational speed 200-3000 RPM bounded");
}

#[test]
fn test_mixed_pump_npsh_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("npsh_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "npsh_bounds",
        "npsh_x10 >= 10 && npsh_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "npsh_check",
        "npsh_x10 >= 10 && npsh_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NPSH x10 meters 10-200 (1.0-20.0m) bounded");
}

#[test]
fn test_mixed_pump_casing_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_valid",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_check",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "casing material 1=cast iron, 2=stainless steel, 3=duplex",
    );
}

#[test]
fn test_mixed_pump_installation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inst", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inst_valid",
        "inst == 1 || inst == 2 || inst == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inst_check",
        "inst == 1 || inst == 2 || inst == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "installation 1=horizontal, 2=vertical, 3=submersible",
    );
}

#[test]
fn test_mixed_pump_impeller_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("imp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "imp_valid",
        "imp == 1 || imp == 2 || imp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "imp_check",
        "imp == 1 || imp == 2 || imp == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller type 1=closed, 2=semi-open, 3=open");
}

#[test]
fn test_mixed_pump_vfd_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vfd", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vfd_valid", "vfd == 0 || vfd == 1"));
    ctx.push_obligation(ProofObligation::assert("vfd_check", "vfd == 0 || vfd == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "variable frequency drive flag boolean (0 or 1)");
}
