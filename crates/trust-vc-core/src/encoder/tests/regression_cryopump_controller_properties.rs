// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_cryopump_pumping_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 100 && speed <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_in_range",
        "speed >= 100 && speed <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pumping speed 10000 (1000.0 L/s) within 100..=100000",
    );
}

#[test]
fn test_cryopump_ultimate_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure >= 1 && pressure <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("pressure_val", "pressure == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_in_range",
        "pressure >= 1 && pressure <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ultimate pressure 1 (0.0001 mbar) within 1..=100");
}

#[test]
fn test_cryopump_cooldown_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooldown", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cooldown_range",
        "cooldown >= 10 && cooldown <= 600",
    ));
    ctx.push_obligation(ProofObligation::assume("cooldown_val", "cooldown == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "cooldown_in_range",
        "cooldown >= 10 && cooldown <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooldown time 60 min within 10..=600");
}

#[test]
fn test_cryopump_first_stage_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp1", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp1_range",
        "temp1 >= 30 && temp1 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("temp1_val", "temp1 == 65"));
    ctx.push_obligation(ProofObligation::assert(
        "temp1_in_range",
        "temp1 >= 30 && temp1 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "first stage temperature 65 K within 30..=100");
}

#[test]
fn test_cryopump_second_stage_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp2", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp2_range",
        "temp2 >= 8 && temp2 <= 25",
    ));
    ctx.push_obligation(ProofObligation::assume("temp2_val", "temp2 == 12"));
    ctx.push_obligation(ProofObligation::assert(
        "temp2_in_range",
        "temp2 >= 8 && temp2 <= 25",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "second stage temperature 12 K within 8..=25");
}

#[test]
fn test_cryopump_regeneration_interval_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("interval", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "interval_range",
        "interval >= 1 && interval <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("interval_val", "interval == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "interval_in_range",
        "interval >= 1 && interval <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "regeneration interval 500 hours within 1..=10000");
}

#[test]
fn test_cryopump_compressor_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("compressor", i32_ty());
    ctx.push_obligation(ProofObligation::assume("compressor_val", "compressor == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "compressor_valid",
        "compressor == 1 || compressor == 2 || compressor == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compressor type 1 (gifford-mcmahon) is valid 3-way enum",
    );
}

#[test]
fn test_cryopump_array_material_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume("material_val", "material == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "material_valid",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "array material 1 (activated-charcoal) is valid 3-way enum",
    );
}

#[test]
fn test_cryopump_regeneration_mode_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "regeneration mode 1 (warm-nitrogen) is valid 3-way enum",
    );
}

#[test]
fn test_cryopump_automatic_regeneration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("auto_regen_enabled", "result == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic regeneration flag==1 implies enabled");
}
