// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_lift_height() {
    let mut ctx = VerificationContext::new();
    for v in &["lift_height", "lift_min", "lift_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lift_val", "lift_height == 25"));
    ctx.push_obligation(ProofObligation::assume("lift_min_val", "lift_min == 1"));
    ctx.push_obligation(ProofObligation::assume("lift_max_val", "lift_max == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "lift_in_range",
        "lift_height >= lift_min && lift_height <= lift_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lift height 25 m within [1, 50]");
}

#[test]
fn test_submergence_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["submergence_x100", "sub_min", "sub_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Submergence ratio x100 (%): 60 = 0.60, range 30-90 (0.30-0.90)
    ctx.push_obligation(ProofObligation::assume("sub_val", "submergence_x100 == 60"));
    ctx.push_obligation(ProofObligation::assume("sub_min_val", "sub_min == 30"));
    ctx.push_obligation(ProofObligation::assume("sub_max_val", "sub_max == 90"));
    ctx.push_obligation(ProofObligation::assert(
        "sub_in_range",
        "submergence_x100 >= sub_min && submergence_x100 <= sub_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "submergence ratio 60 (0.60) within [30, 90]");
}

#[test]
fn test_air_flow_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["air_flow_x10", "air_min", "air_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Air flow rate x10 (L/min): 500 = 50.0 L/min, range 10-10000 (1.0-1000.0)
    ctx.push_obligation(ProofObligation::assume("air_val", "air_flow_x10 == 500"));
    ctx.push_obligation(ProofObligation::assume("air_min_val", "air_min == 10"));
    ctx.push_obligation(ProofObligation::assume("air_max_val", "air_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "air_in_range",
        "air_flow_x10 >= air_min && air_flow_x10 <= air_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air flow rate 500 (50.0 L/min) within [10, 10000]");
}

#[test]
fn test_pipe_diameter() {
    let mut ctx = VerificationContext::new();
    for v in &["pipe_dia_x10", "dia_min", "dia_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pipe diameter x10 (mm): 500 = 50.0 mm, range 20-3000 (2.0-300.0)
    ctx.push_obligation(ProofObligation::assume("dia_val", "pipe_dia_x10 == 500"));
    ctx.push_obligation(ProofObligation::assume("dia_min_val", "dia_min == 20"));
    ctx.push_obligation(ProofObligation::assume("dia_max_val", "dia_max == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "dia_in_range",
        "pipe_dia_x10 >= dia_min && pipe_dia_x10 <= dia_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pipe diameter 500 (50.0 mm) within [20, 3000]");
}

#[test]
fn test_water_flow_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["water_flow_x10", "water_min", "water_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Water flow rate x10 (L/min): 200 = 20.0 L/min, range 1-5000 (0.1-500.0)
    ctx.push_obligation(ProofObligation::assume(
        "water_val",
        "water_flow_x10 == 200",
    ));
    ctx.push_obligation(ProofObligation::assume("water_min_val", "water_min == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "water_max_val",
        "water_max == 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "water_in_range",
        "water_flow_x10 >= water_min && water_flow_x10 <= water_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "water flow rate 200 (20.0 L/min) within [1, 5000]");
}

#[test]
fn test_air_injection_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("injection_method", u32_ty());
    // Air injection methods: 1=open-pipe, 2=diffuser, 3=venturi
    ctx.push_obligation(ProofObligation::assume("inj_val", "injection_method == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_injection",
        "injection_method == 1 || injection_method == 2 || injection_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "injection method 2=diffuser is valid (3-way disjunction)",
    );
}

#[test]
fn test_pipe_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pipe_material", u32_ty());
    // Pipe materials: 1=PVC, 2=stainless, 3=HDPE
    ctx.push_obligation(ProofObligation::assume("mat_val", "pipe_material == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "pipe_material == 1 || pipe_material == 2 || pipe_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pipe material 3=HDPE is valid (3-way disjunction)");
}

#[test]
fn test_flow_regime_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_regime", u32_ty());
    // Flow regimes: 1=slug, 2=churn, 3=annular
    ctx.push_obligation(ProofObligation::assume("regime_val", "flow_regime == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_regime",
        "flow_regime == 1 || flow_regime == 2 || flow_regime == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow regime 1=slug is valid (3-way disjunction)");
}

#[test]
fn test_number_of_stages_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["num_stages", "stages_min", "stages_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of stages: bounded 1-4
    ctx.push_obligation(ProofObligation::assume("stages_val", "num_stages == 2"));
    ctx.push_obligation(ProofObligation::assume("stages_min_val", "stages_min == 1"));
    ctx.push_obligation(ProofObligation::assume("stages_max_val", "stages_max == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "stages_in_range",
        "num_stages >= stages_min && num_stages <= stages_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of stages 2 within [1, 4]");
}

#[test]
fn test_automatic_air_regulation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_regulation", i32_ty());
    // Automatic air regulation: boolean flag (0=disabled, 1=enabled)
    ctx.push_obligation(ProofObligation::assume(
        "flag_enabled",
        "auto_regulation == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "regulation_valid",
        "auto_regulation == 1 || auto_regulation == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic air regulation flag is boolean (enabled)",
    );
}
