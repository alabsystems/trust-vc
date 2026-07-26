// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_feed_rate_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["rate", "rate_min", "rate_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Feed rate in kg/h: value 500, valid range 1 to 10000
    ctx.push_obligation(ProofObligation::assume("fr_val", "rate == 500"));
    ctx.push_obligation(ProofObligation::assume("fr_min", "rate_min == 1"));
    ctx.push_obligation(ProofObligation::assume("fr_max", "rate_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "fr_in_range",
        "rate >= rate_min && rate <= rate_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 500 kg/h in range [1,10000]");
}

#[test]
fn test_screw_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["diameter", "dia_min", "dia_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Screw diameter in mm: value 200, valid range 25 to 600
    ctx.push_obligation(ProofObligation::assume("sd_val", "diameter == 200"));
    ctx.push_obligation(ProofObligation::assume("sd_min", "dia_min == 25"));
    ctx.push_obligation(ProofObligation::assume("sd_max", "dia_max == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "sd_in_range",
        "diameter >= dia_min && diameter <= dia_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screw diameter 200 mm in range [25,600]");
}

#[test]
fn test_screw_speed_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["speed", "speed_min", "speed_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Screw speed in RPM: value 60, valid range 5 to 300
    ctx.push_obligation(ProofObligation::assume("ss_val", "speed == 60"));
    ctx.push_obligation(ProofObligation::assume("ss_min", "speed_min == 5"));
    ctx.push_obligation(ProofObligation::assume("ss_max", "speed_max == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "ss_in_range",
        "speed >= speed_min && speed <= speed_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screw speed 60 RPM in range [5,300]");
}

#[test]
fn test_screw_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("screw_type", u32_ty());
    ctx.declare_var_typed("valid_st", i32_ty());
    // Screw types: 1=single flight, 2=double flight, 3=variable pitch
    ctx.push_obligation(ProofObligation::assume("st_val", "screw_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "st_def",
        "valid_st == if screw_type == 1 || screw_type == 2 || screw_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("st_chk", "valid_st == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "screw type 1 (single flight) is valid screw feeder type",
    );
}

#[test]
fn test_drive_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drv_type", u32_ty());
    ctx.declare_var_typed("valid_dt", i32_ty());
    // Drive types: 1=direct, 2=gear reduction, 3=belt drive
    ctx.push_obligation(ProofObligation::assume("dt_val", "drv_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "dt_def",
        "valid_dt == if drv_type == 1 || drv_type == 2 || drv_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dt_chk", "valid_dt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive type 1 (direct) is valid screw feeder drive");
}

#[test]
fn test_accuracy_scaled() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x10", "acc_min", "acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Accuracy as x10 %: value 5 (0.5%), valid range 1 (0.1%) to 50 (5.0%)
    ctx.push_obligation(ProofObligation::assume("ac_val", "accuracy_x10 == 5"));
    ctx.push_obligation(ProofObligation::assume("ac_min", "acc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ac_max", "acc_max == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "ac_in_range",
        "accuracy_x10 >= acc_min && accuracy_x10 <= acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 5 (0.5%) in range [1,50] (0.1%-5.0%)");
}

#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["power", "power_min", "power_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Motor power in W: value 7500, valid range 100 to 75000
    ctx.push_obligation(ProofObligation::assume("mp_val", "power == 7500"));
    ctx.push_obligation(ProofObligation::assume("mp_min", "power_min == 100"));
    ctx.push_obligation(ProofObligation::assume("mp_max", "power_max == 75000"));
    ctx.push_obligation(ProofObligation::assert(
        "mp_in_range",
        "power >= power_min && power <= power_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 7500 W in range [100,75000]");
}

#[test]
fn test_trough_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.declare_var_typed("valid_mat", i32_ty());
    // Trough material: 1=carbon steel, 2=stainless 304, 3=stainless 316
    ctx.push_obligation(ProofObligation::assume("tm_val", "material == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tm_def",
        "valid_mat == if material == 1 || material == 2 || material == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tm_chk", "valid_mat == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trough material 1 (carbon steel) is valid material",
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
fn test_loss_in_weight_mode_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("liw_flag", i32_ty());
    ctx.declare_var_typed("liw_active", i32_ty());
    // Loss-in-weight mode: boolean flag 1=enabled
    ctx.push_obligation(ProofObligation::assume("lw_val", "liw_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "lw_def",
        "liw_active == if liw_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("lw_chk", "liw_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "loss-in-weight mode flag=1 is active");
}
