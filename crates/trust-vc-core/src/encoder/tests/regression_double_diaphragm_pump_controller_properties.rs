// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flow_rate_scaled_bounded() {
    // Flow rate in ×10 L/min (0.1 L/min resolution)
    // 150 means 15.0 L/min, must be in [1, 10000] (0.1 to 1000.0 L/min)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate_x10 == 150")); // 15.0 L/min
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if flow_rate_x10 >= 1 && flow_rate_x10 <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AODD flow: 150 (15.0 L/min) in [1, 10000]");
}

#[test]
fn max_pressure_bounded() {
    // Max operating pressure in bar, bounded [5, 12]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_pressure_bar", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mp", "max_pressure_bar == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if max_pressure_bar >= 5 && max_pressure_bar <= 12 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AODD pressure: 8 bar in [5, 12]");
}

#[test]
fn port_size_bounded() {
    // Port size in mm, bounded [6, 100]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("port_size_mm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ps", "port_size_mm == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if port_size_mm >= 6 && port_size_mm <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AODD port: 25mm in [6, 100]");
}

#[test]
fn stroke_count_bounded() {
    // Stroke count in strokes/min, bounded [10, 300]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_count", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sc", "stroke_count == 120"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if stroke_count >= 10 && stroke_count <= 300 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AODD strokes: 120/min in [10, 300]");
}

#[test]
fn air_consumption_scaled_bounded() {
    // Air consumption in ×10 L/min (0.1 L/min resolution)
    // 500 means 50.0 L/min, must be in [1, 20000] (0.1 to 2000.0 L/min)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_consumption_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ac", "air_consumption_x10 == 500")); // 50.0 L/min
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if air_consumption_x10 >= 1 && air_consumption_x10 <= 20000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AODD air: 500 (50.0 L/min) in [1, 20000]");
}

#[test]
fn diaphragm_material_valid() {
    // 1=santoprene, 2=PTFE, 3=Buna-N
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diaphragm_material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dm", "diaphragm_material == 2")); // PTFE
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "diaphragm_material == 1 || diaphragm_material == 2 || diaphragm_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AODD diaphragm: PTFE (2) in {1,2,3}");
}

#[test]
fn wetted_body_material_valid() {
    // 1=polypropylene, 2=aluminum, 3=stainless steel
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wetted_body", u32_ty());
    ctx.push_obligation(ProofObligation::assume("wb", "wetted_body == 3")); // stainless steel
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "wetted_body == 1 || wetted_body == 2 || wetted_body == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AODD body: stainless steel (3) in {1,2,3}");
}

#[test]
fn valve_type_valid() {
    // 1=flap, 2=ball, 3=poppet
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vt", "valve_type == 2")); // ball
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "valve_type == 1 || valve_type == 2 || valve_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AODD valve: ball (2) in {1,2,3}");
}

#[test]
fn solids_passage_bounded() {
    // Solids passage in mm, bounded [1, 75]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("solids_passage_mm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sp", "solids_passage_mm == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if solids_passage_mm >= 1 && solids_passage_mm <= 75 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AODD solids: 12mm in [1, 75]");
}

#[test]
fn deadhead_capable_flag() {
    // Boolean flag: 1=deadhead capable, 0=not capable
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("deadhead_capable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dh", "deadhead_capable == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "is_true",
        "deadhead_capable == if deadhead_capable == 1 { 1 } else { 0 }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AODD deadhead: capable (flag=1)");
}
