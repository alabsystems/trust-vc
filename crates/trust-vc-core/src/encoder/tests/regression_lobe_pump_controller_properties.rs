// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Lobe pump controller verification properties.
/// Models key parameters of rotary lobe pumps used in sanitary
/// and process applications (food, pharma, chemical transfer).

// 1. Flow rate scaled x10 (m^3/h), range 1-5000 => 0.1-500.0 m^3/h
#[test]
fn test_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 50.0 m3/h (500 x10) in [1, 5000]");
}

// 2. Max pressure scaled x10 (bar), range 1-150 => 0.1-15.0 bar
#[test]
fn test_max_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 1 && press_x10 <= 150",
    ));
    ctx.push_obligation(ProofObligation::assume("press_val", "press_x10 == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press_x10 >= 1 && press_x10 <= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure 10.0 bar (100 x10) in [1, 150]");
}

// 3. Rotor speed (RPM), range 50-1200
#[test]
fn test_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 50 && speed <= 1200",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 400"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 50 && speed <= 1200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed 400 RPM in [50, 1200]");
}

// 4. Displacement per revolution scaled x10 (L/rev), range 1-1000 => 0.1-100.0 L/rev
#[test]
fn test_displacement_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disp_range",
        "disp_x10 >= 1 && disp_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("disp_val", "disp_x10 == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "disp_bounded",
        "disp_x10 >= 1 && disp_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement 20.0 L/rev (200 x10) in [1, 1000]");
}

// 5. Lobe count per rotor, range 2-4
#[test]
fn test_lobe_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lobes", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lobe_range",
        "lobes >= 2 && lobes <= 4",
    ));
    ctx.push_obligation(ProofObligation::assume("lobe_val", "lobes == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "lobe_bounded",
        "lobes >= 2 && lobes <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lobe count 3 in [2, 4]");
}

// 6. Clearance scaled x100 (mm), range 1-100 => 0.01-1.00 mm
#[test]
fn test_clearance_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("clear_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "clear_range",
        "clear_x100 >= 1 && clear_x100 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("clear_val", "clear_x100 == 15"));
    ctx.push_obligation(ProofObligation::assert(
        "clear_bounded",
        "clear_x100 >= 1 && clear_x100 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clearance 0.15 mm (15 x100) in [1, 100]");
}

// 7. Rotor material: 1=stainless, 2=rubber-coated, 3=PTFE-coated
#[test]
fn test_rotor_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "material_valid",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "material_in_range",
        "material >= 1 && material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor material 3-way disjunction");
}

// 8. Surface finish: 1=polished, 2=sandblasted, 3=electropolished
#[test]
fn test_surface_finish_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("finish", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "finish_valid",
        "finish == 1 || finish == 2 || finish == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "finish_in_range",
        "finish >= 1 && finish <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "surface finish 3-way disjunction");
}

// 9. CIP connection type: 1=clamp, 2=threaded, 3=flanged
#[test]
fn test_cip_connection_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "conn_valid",
        "conn == 1 || conn == 2 || conn == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "conn_in_range",
        "conn >= 1 && conn <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CIP connection 3-way disjunction");
}

// 10. Reversible operation boolean flag: i32, 0 or 1; assert reversible when flag is 1
#[test]
fn test_reversible_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reversible", i32_ty());
    ctx.push_obligation(ProofObligation::assume("reversible_val", "reversible == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "is_reversible",
        "if reversible == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reversible boolean flag");
}
