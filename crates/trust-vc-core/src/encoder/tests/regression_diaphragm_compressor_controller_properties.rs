// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_diaphragm_compressor_stroke_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "rate >= 100 && rate <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rate_bounded",
        "rate >= 100 && rate <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "stroke rate must be between 100 and 1500 strokes/min",
    );
}

#[test]
fn test_diaphragm_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure >= 1 && pressure <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure >= 1 && pressure <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure must be between 1 and 5000 bar");
}

#[test]
fn test_diaphragm_compressor_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power >= 1 && power <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power >= 1 && power <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power must be between 1 and 500 kW");
}

#[test]
fn test_diaphragm_compressor_flow_rate_scaled_bounded() {
    // flow_rate_x10 represents 0.1-5000.0 Nm3/h scaled by 10
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate x10 must be between 1 and 50000 (representing 0.1-5000.0 Nm3/h)",
    );
}

#[test]
fn test_diaphragm_compressor_deflection_scaled_bounded() {
    // deflection_x100 represents 0.10-5.00 mm scaled by 100
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("deflection_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "deflection_range",
        "deflection_x100 >= 10 && deflection_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "deflection_bounded",
        "deflection_x100 >= 10 && deflection_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "diaphragm deflection x100 must be between 10 and 500 (representing 0.10-5.00 mm)",
    );
}

#[test]
fn test_diaphragm_compressor_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stages_range",
        "stages >= 1 && stages <= 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stages_bounded",
        "stages >= 1 && stages <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "number of compression stages must be between 1 and 4",
    );
}

#[test]
fn test_diaphragm_compressor_diaphragm_material_valid() {
    // 1=stainless-steel, 2=inconel, 3=hastelloy
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "material_valid",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "material_disjunction",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "diaphragm material must be stainless-steel(1), inconel(2), or hastelloy(3)",
    );
}

#[test]
fn test_diaphragm_compressor_cooling_method_valid() {
    // 1=air, 2=water, 3=oil
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cooling_valid",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cooling_disjunction",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling method must be air(1), water(2), or oil(3)",
    );
}

#[test]
fn test_diaphragm_compressor_sealing_type_valid() {
    // 1=static-oring, 2=metal-to-metal, 3=lip-seal
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sealing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sealing_valid",
        "sealing == 1 || sealing == 2 || sealing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sealing_disjunction",
        "sealing == 1 || sealing == 2 || sealing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sealing type must be static-oring(1), metal-to-metal(2), or lip-seal(3)",
    );
}

#[test]
fn test_diaphragm_compressor_auto_leak_detection_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leak_detect", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "leak_detect_flag",
        "leak_detect == 0 || leak_detect == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "leak_detect_boolean",
        "leak_detect == 0 || leak_detect == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic leak detection must be a boolean flag (0=off, 1=on)",
    );
}
