// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// ---------- bounded-range tests (positive displacement screw pump) ----------

#[test]
fn flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "flow_x10 >= 1 && flow_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "flow_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "flow_x10 >= 1 && flow_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 (100.0 m3/h) within [1, 10000]");
}

#[test]
fn max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "pressure >= 10 && pressure <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "pressure == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "pressure >= 10 && pressure <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max discharge pressure 100 bar within [10, 200]");
}

#[test]
fn speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "speed >= 100 && speed <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "speed == 1500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "speed >= 100 && speed <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screw speed 1500 RPM within [100, 4000]");
}

#[test]
fn displacement_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "disp_x10 >= 1 && disp_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "disp_x10 == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "disp_x10 >= 1 && disp_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement x10 (80.0 L/rev) within [1, 5000]");
}

#[test]
fn screw_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("screws", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "screws >= 1 && screws <= 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "screws == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "screws >= 1 && screws <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "twin-screw (2) within [1, 3] screw count");
}

#[test]
fn viscosity_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("viscosity", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "viscosity >= 100 && viscosity <= 5000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "viscosity == 1000000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "viscosity >= 100 && viscosity <= 5000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "viscosity 1000000 cSt within [100, 5000000]");
}

// ---------- disjunction tests (enum-like screw pump configuration) ----------

#[test]
fn screw_profile_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("profile", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "profile == 1 || profile == 2 || profile == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "profile >= 1 && profile <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "screw profile (1=equal-pitch, 2=progressive, 3=variable) in [1, 3]",
    );
}

#[test]
fn housing_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "material >= 1 && material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "housing material (1=cast-iron, 2=stainless, 3=duplex) in [1, 3]",
    );
}

#[test]
fn timing_gear_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gear", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "gear == 1 || gear == 2 || gear == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "gear >= 1 && gear <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "timing gear (1=external, 2=internal, 3=none) in [1, 3]",
    );
}

#[test]
fn self_priming_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "priming",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "self-priming flag set yields 1");
}
