// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_belt_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width", i32_ty());
    ctx.push_obligation(ProofObligation::assume("width_val", "width == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "width_range",
        "width >= 500 && width <= 3500",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "width >= 500"));
    ctx.push_obligation(ProofObligation::assert("upper", "width <= 3500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt width (mm) 2000 in [500, 3500] implies bounds hold",
    );
}

#[test]
fn test_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "throughput_val",
        "throughput == 50",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "throughput_range",
        "throughput >= 1 && throughput <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "throughput >= 1"));
    ctx.push_obligation(ProofObligation::assert("upper", "throughput <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "throughput (m³/h) 50 in [1, 200] implies bounds hold",
    );
}

#[test]
fn test_belt_speed_bounded() {
    // Belt speed scaled ×10: 3.0 m/min → 30, range [5, 100]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed_x10 == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed_x10 >= 5 && speed_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "speed_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("upper", "speed_x10 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt speed (×10 m/min) 30 in [5, 100] implies bounds hold",
    );
}

#[test]
fn test_press_type_three_way_disjunction() {
    // 1=gravity, 2=pressure, 3=high-pressure
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_press_type",
        "press_type == 1 || press_type == 2 || press_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "press_type >= 1 && press_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "press type {1=gravity,2=pressure,3=high-pressure} implies [1,3] bounds",
    );
}

#[test]
fn test_belt_material_three_way_disjunction() {
    // 1=polyester, 2=polypropylene, 3=stainless mesh
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_material",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "material >= 1 && material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt material {1=polyester,2=polypropylene,3=stainless mesh} implies [1,3] bounds",
    );
}

#[test]
fn test_cake_solids_bounded() {
    // Cake solids scaled ×10: 25.0% → 250, range [100, 500]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("solids_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("solids_val", "solids_x10 == 250"));
    ctx.push_obligation(ProofObligation::assume(
        "solids_range",
        "solids_x10 >= 100 && solids_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "solids_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("upper", "solids_x10 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cake solids (×10 %) 250 in [100, 500] implies bounds hold",
    );
}

#[test]
fn test_wash_water_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wash", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wash_val", "wash == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "wash_range",
        "wash >= 10 && wash <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "wash >= 10"));
    ctx.push_obligation(ProofObligation::assert("upper", "wash <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wash water flow (L/min) 100 in [10, 500] implies bounds hold",
    );
}

#[test]
fn test_belt_tension_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tension", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tension_val", "tension == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "tension_range",
        "tension >= 5 && tension <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "tension >= 5"));
    ctx.push_obligation(ProofObligation::assert("upper", "tension <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "belt tension (kN) 30 in [5, 100] implies bounds hold",
    );
}

#[test]
fn test_polymer_dosing_bounded() {
    // Polymer dosing scaled ×10: 5.0 mg/L → 50, range [5, 200]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dose_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dose_val", "dose_x10 == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "dose_range",
        "dose_x10 >= 5 && dose_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert("lower", "dose_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("upper", "dose_x10 <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "polymer dosing (×10 mg/L) 50 in [5, 200] implies bounds hold",
    );
}

#[test]
fn test_belt_tracking_boolean_flag() {
    // Boolean flag encoded as i32: 1=tracking active
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "active_def",
        "active == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tracking_active", "active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt tracking flag=1 implies active==1");
}
