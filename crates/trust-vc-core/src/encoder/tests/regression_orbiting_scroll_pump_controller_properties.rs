// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// ---------- bounded-range tests (orbiting scroll vacuum pump) ----------

#[test]
fn pumping_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "speed_x10 >= 10 && speed_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "speed_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "speed_x10 >= 10 && speed_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pumping speed x10 (100.0 L/min) within [10, 50000]",
    );
}

#[test]
fn ultimate_pressure_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "pressure_x1000 >= 1 && pressure_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "pressure_x1000 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "pressure_x1000 >= 1 && pressure_x1000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ultimate pressure x1000 (0.010 mbar) within [1, 1000]",
    );
}

#[test]
fn max_inlet_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "inlet_x10 >= 1 && inlet_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "inlet_x10 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "inlet_x10 >= 1 && inlet_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max inlet pressure x10 (1.0 bar) within [1, 100]");
}

#[test]
fn orbit_radius_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("radius_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "radius_x100 >= 10 && radius_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "radius_x100 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "radius_x100 >= 10 && radius_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "orbit radius x100 (0.50 mm) within [10, 500]");
}

#[test]
fn motor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "motor_rpm >= 500 && motor_rpm <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "motor_rpm == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "motor_rpm >= 500 && motor_rpm <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor speed 3000 RPM within [500, 5000]");
}

#[test]
fn number_of_wraps_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wraps", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "wraps >= 1 && wraps <= 5"));
    ctx.push_obligation(ProofObligation::assume("val", "wraps == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "wraps >= 1 && wraps <= 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of wraps (3) within [1, 5]");
}

// ---------- disjunction tests (enum-like scroll pump configuration) ----------

#[test]
fn scroll_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "material == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "material >= 1 && material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scroll material (1=aluminum, 2=cast-iron, 3=stainless) in [1, 3]",
    );
}

#[test]
fn tip_seal_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "seal == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "seal >= 1 && seal <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tip seal type (1=PTFE, 2=polymer, 3=labyrinth) in [1, 3]",
    );
}

#[test]
fn cooling_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "cooling == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "cooling >= 1 && cooling <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling method (1=air, 2=water, 3=oil-injection) in [1, 3]",
    );
}

#[test]
fn automatic_gas_ballast_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "ballast",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic gas ballast flag set yields 1");
}
