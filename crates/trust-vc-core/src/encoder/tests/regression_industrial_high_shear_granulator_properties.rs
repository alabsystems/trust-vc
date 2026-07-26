// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Industrial high shear granulator verification properties
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_bowl_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bowl_volume", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "bowl_volume >= 5 && bowl_volume <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "bowl_volume == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "bowl_volume >= 5 && bowl_volume <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl volume 300 L within 5-2000 L range");
}

#[test]
fn test_impeller_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impeller_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "impeller_speed >= 50 && impeller_speed <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "impeller_speed == 400"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "impeller_speed >= 50 && impeller_speed <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller speed 400 RPM within 50-1500 RPM range");
}

#[test]
fn test_chopper_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chopper_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "chopper_speed >= 500 && chopper_speed <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "chopper_speed == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "chopper_speed >= 500 && chopper_speed <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chopper speed 3000 RPM within 500-5000 RPM range");
}

#[test]
fn test_batch_size_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batch_size_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "batch_size_x10 >= 10 && batch_size_x10 <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "batch_size_x10 == 2000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "batch_size_x10 >= 10 && batch_size_x10 <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "batch size 200.0 kg (x10) within 1.0-2000.0 kg range",
    );
}

#[test]
fn test_granulation_time_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("granulation_time_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "granulation_time_x10 >= 10 && granulation_time_x10 <= 600",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "granulation_time_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "granulation_time_x10 >= 10 && granulation_time_x10 <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "granulation time 5.0 min (x10) within 1.0-60.0 min range",
    );
}

#[test]
fn test_torque_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "torque_x10 >= 10 && torque_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "torque_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "torque_x10 >= 10 && torque_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "torque 500.0 Nm (x10) within 1.0-5000.0 Nm range");
}

#[test]
fn test_blade_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blade_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "blade_type == 1 || blade_type == 2 || blade_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "blade_type >= 1 && blade_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "blade type 1=flat 2=plowshare 3=star within valid range",
    );
}

#[test]
fn test_chopper_style_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chopper_style", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "chopper_style == 1 || chopper_style == 2 || chopper_style == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "chopper_style >= 1 && chopper_style <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "chopper style 1=knife 2=saw-tooth 3=cross within valid range",
    );
}

#[test]
fn test_discharge_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "discharge_type == 1 || discharge_type == 2 || discharge_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "discharge_type >= 1 && discharge_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge type 1=bottom 2=tilting 3=side within valid range",
    );
}

#[test]
fn test_vacuum_drying_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_drying", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag", "vacuum_drying == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "enabled",
        "if vacuum_drying == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum drying flag enabled when set to 1");
}
