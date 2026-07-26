// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_lmi_max_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity", i32_ty());
    ctx.push_obligation(ProofObligation::assume("capacity_val", "capacity == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "capacity_bounded",
        "capacity >= 1 && capacity <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max capacity 100 t within [1, 1000]");
}

#[test]
fn test_lmi_boom_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("boom", i32_ty());
    ctx.push_obligation(ProofObligation::assume("boom_val", "boom == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "boom_bounded",
        "boom >= 5 && boom <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boom length 50 m within [5, 200]");
}

#[test]
fn test_lmi_radius_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("radius_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("radius_val", "radius_x10 == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "radius_bounded",
        "radius_x10 >= 10 && radius_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "radius 15.0 m (x10=150) within [10, 500]");
}

#[test]
fn test_lmi_crane_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("crane_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("crane_val", "crane_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_crane_type",
        "crane_type == 1 || crane_type == 2 || crane_type == 3 || crane_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "crane type 1 (mobile) is one of {1=mobile, 2=tower, 3=crawler, 4=offshore}",
    );
}

#[test]
fn test_lmi_load_cell_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cells", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cells_val", "cells == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "cells_bounded",
        "cells >= 1 && cells <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "load cell count 4 within [1, 8]");
}

#[test]
fn test_lmi_accuracy_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_val",
        "accuracy_x10 == 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_bounded",
        "accuracy_x10 >= 5 && accuracy_x10 <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 1.0% (x10=10) within [5, 30]");
}

#[test]
fn test_lmi_wind_speed_limit_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wind", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wind_val", "wind == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "wind_bounded",
        "wind >= 5 && wind <= 40",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wind speed limit 20 m/s within [5, 40]");
}

#[test]
fn test_lmi_display_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("display", i32_ty());
    ctx.push_obligation(ProofObligation::assume("display_val", "display == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_display_type",
        "display == 1 || display == 2 || display == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "display type 2 (LCD) is one of {1=LED bar, 2=LCD, 3=touchscreen}",
    );
}

#[test]
fn test_lmi_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 460 && temp <= 570",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 20C (offset+500=520) within [460, 570]",
    );
}

#[test]
fn test_lmi_anti_two_block_enabled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("atb_enabled", "result == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anti-two-block flag enabled (flag=1 -> result=1)");
}
