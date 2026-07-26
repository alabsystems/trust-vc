// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["flow", "flow_min", "flow_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Flow rate in L/h
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow == 5000"));
    ctx.push_obligation(ProofObligation::assume("flow_min_val", "flow_min == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "flow_max_val",
        "flow_max == 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_in_range",
        "flow >= flow_min && flow <= flow_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 5000 L/h within [100, 100000]");
}

#[test]
fn test_differential_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["dp", "dp_min", "dp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Differential pressure in bar
    ctx.push_obligation(ProofObligation::assume("dp_val", "dp == 8"));
    ctx.push_obligation(ProofObligation::assume("dp_min_val", "dp_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dp_max_val", "dp_max == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "dp_in_range",
        "dp >= dp_min && dp <= dp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "differential pressure 8 bar within [1, 20]");
}

#[test]
fn test_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["speed", "speed_min", "speed_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Rotor speed in RPM
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 200"));
    ctx.push_obligation(ProofObligation::assume("speed_min_val", "speed_min == 10"));
    ctx.push_obligation(ProofObligation::assume("speed_max_val", "speed_max == 600"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_in_range",
        "speed >= speed_min && speed <= speed_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed 200 RPM within [10, 600]");
}

#[test]
fn test_lobe_count_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lobes", u32_ty());
    // Lobe count: 2, 3, or 4
    ctx.push_obligation(ProofObligation::assume("lobes_val", "lobes == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_lobes",
        "lobes == 2 || lobes == 3 || lobes == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lobe count 3 is valid (3-way disjunction)");
}

#[test]
fn test_seal_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", u32_ty());
    // Seal types: 1=single mechanical, 2=double mechanical, 3=lip seal
    ctx.push_obligation(ProofObligation::assume("seal_val", "seal_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_seal",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seal type 2=double mechanical is valid (3-way disjunction)",
    );
}

#[test]
fn test_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    // Materials: 1=SS316, 2=SS304, 3=duplex steel
    ctx.push_obligation(ProofObligation::assume("material_val", "material == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "material 1=SS316 is valid (3-way disjunction)");
}

#[test]
fn test_surface_finish_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["finish_x100", "finish_min", "finish_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Surface finish in Ra um x100: 80 = 0.80 Ra um
    ctx.push_obligation(ProofObligation::assume("finish_val", "finish_x100 == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "finish_min_val",
        "finish_min == 10",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "finish_max_val",
        "finish_max == 320",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "finish_in_range",
        "finish_x100 >= finish_min && finish_x100 <= finish_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "surface finish 0.80 Ra um (x100=80) within [10, 320]",
    );
}

#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["power", "power_min", "power_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Motor power in kW
    ctx.push_obligation(ProofObligation::assume("power_val", "power == 15"));
    ctx.push_obligation(ProofObligation::assume("power_min_val", "power_min == 1"));
    ctx.push_obligation(ProofObligation::assume("power_max_val", "power_max == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "power_in_range",
        "power >= power_min && power <= power_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 15 kW within [1, 150]");
}

#[test]
fn test_cip_rated_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cip_flag", i32_ty());
    ctx.declare_var_typed("cip_result", i32_ty());
    // CIP (clean-in-place) rated: flag=1 means enabled
    ctx.push_obligation(ProofObligation::assume("flag_val", "cip_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "cip_result == if cip_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cip_active", "cip_result == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CIP rated flag enabled: if 1 then 1 else 0 == 1");
}

#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["temp", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating temperature with +500 offset: 530 = 30C, 460 = -40C, 640 = 140C
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 530"));
    ctx.push_obligation(ProofObligation::assume("temp_min_val", "temp_min == 460"));
    ctx.push_obligation(ProofObligation::assume("temp_max_val", "temp_max == 640"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "temp >= temp_min && temp <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 30C (offset 530) within [-40C, 140C] (offset [460, 640])",
    );
}
