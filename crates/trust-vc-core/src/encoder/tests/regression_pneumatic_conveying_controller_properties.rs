// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_conveying_rate_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["rate", "rate_min", "rate_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Conveying rate in t/h: value 20, valid range 1 to 200
    ctx.push_obligation(ProofObligation::assume("cr_val", "rate == 20"));
    ctx.push_obligation(ProofObligation::assume("cr_min", "rate_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cr_max", "rate_max == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "cr_in_range",
        "rate >= rate_min && rate <= rate_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conveying rate 20 t/h in range [1,200]");
}

#[test]
fn test_pipeline_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["diameter", "dia_min", "dia_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pipeline diameter in mm: value 150, valid range 50 to 500
    ctx.push_obligation(ProofObligation::assume("pd_val", "diameter == 150"));
    ctx.push_obligation(ProofObligation::assume("pd_min", "dia_min == 50"));
    ctx.push_obligation(ProofObligation::assume("pd_max", "dia_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "pd_in_range",
        "diameter >= dia_min && diameter <= dia_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pipeline diameter 150 mm in range [50,500]");
}

#[test]
fn test_air_velocity_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["velocity", "vel_min", "vel_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Air velocity in m/s: value 25, valid range 5 to 40
    ctx.push_obligation(ProofObligation::assume("av_val", "velocity == 25"));
    ctx.push_obligation(ProofObligation::assume("av_min", "vel_min == 5"));
    ctx.push_obligation(ProofObligation::assume("av_max", "vel_max == 40"));
    ctx.push_obligation(ProofObligation::assert(
        "av_in_range",
        "velocity >= vel_min && velocity <= vel_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air velocity 25 m/s in range [5,40]");
}

#[test]
fn test_conveying_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conv_mode", u32_ty());
    ctx.declare_var_typed("valid_cm", i32_ty());
    // Conveying modes: 1=dilute phase, 2=dense phase, 3=semi-dense
    ctx.push_obligation(ProofObligation::assume("cm_val", "conv_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "valid_cm == if conv_mode == 1 || conv_mode == 2 || conv_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cm_chk", "valid_cm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conveying mode 1 (dilute phase) is valid mode");
}

#[test]
fn test_blower_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blower_type", u32_ty());
    ctx.declare_var_typed("valid_bt", i32_ty());
    // Blower types: 1=roots, 2=screw, 3=centrifugal
    ctx.push_obligation(ProofObligation::assume("bt_val", "blower_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "bt_def",
        "valid_bt == if blower_type == 1 || blower_type == 2 || blower_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("bt_chk", "valid_bt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "blower type 1 (roots) is valid blower type");
}

#[test]
fn test_system_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["pressure", "press_min", "press_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // System pressure in kPa: value 200, valid range 20 to 600
    ctx.push_obligation(ProofObligation::assume("sp_val", "pressure == 200"));
    ctx.push_obligation(ProofObligation::assume("sp_min", "press_min == 20"));
    ctx.push_obligation(ProofObligation::assume("sp_max", "press_max == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "sp_in_range",
        "pressure >= press_min && pressure <= press_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "system pressure 200 kPa in range [20,600]");
}

#[test]
fn test_pipeline_length_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["length", "len_min", "len_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pipeline length in m: value 100, valid range 5 to 500
    ctx.push_obligation(ProofObligation::assume("pl_val", "length == 100"));
    ctx.push_obligation(ProofObligation::assume("pl_min", "len_min == 5"));
    ctx.push_obligation(ProofObligation::assume("pl_max", "len_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "pl_in_range",
        "length >= len_min && length <= len_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pipeline length 100 m in range [5,500]");
}

#[test]
fn test_material_handling_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat_type", u32_ty());
    ctx.declare_var_typed("valid_mt", i32_ty());
    // Material types: 1=powder, 2=granule, 3=pellet, 4=flake
    ctx.push_obligation(ProofObligation::assume("mt_val", "mat_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "mt_def",
        "valid_mt == if mat_type == 1 || mat_type == 2 || mat_type == 3 || mat_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("mt_chk", "valid_mt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "material type 1 (powder) is valid material handling type",
    );
}

#[test]
fn test_operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["temp", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating temperature offset +500: value 540 (40C), valid range 460 (-40C) to 600 (100C)
    ctx.push_obligation(ProofObligation::assume("ot_val", "temp == 540"));
    ctx.push_obligation(ProofObligation::assume("ot_min", "temp_min == 460"));
    ctx.push_obligation(ProofObligation::assume("ot_max", "temp_max == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "ot_in_range",
        "temp >= temp_min && temp <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 540 (40C) in range [460,600] (-40C to 100C)",
    );
}

#[test]
fn test_diverter_valve_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dv_flag", i32_ty());
    ctx.declare_var_typed("dv_active", i32_ty());
    // Diverter valve: boolean flag 1=enabled
    ctx.push_obligation(ProofObligation::assume("dv_val", "dv_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "dv_def",
        "dv_active == if dv_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dv_chk", "dv_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "diverter valve flag=1 is active");
}
