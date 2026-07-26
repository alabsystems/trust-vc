// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Regression tests: side channel pump controller properties

use super::*;

#[test]
fn test_side_channel_pump_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "flow_x10 >= 1 && flow_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "flow_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "flow_x10 >= 1 && flow_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 L/min bounded 1-500 at 5.0 L/min");
}

#[test]
fn test_side_channel_pump_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "pressure_x10 >= 10 && pressure_x10 <= 250",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "pressure_x10 == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "pressure_x10 >= 10 && pressure_x10 <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure x10 bar bounded 10-250 at 15.0 bar");
}

#[test]
fn test_side_channel_pump_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "speed >= 1000 && speed <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "speed == 2900"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "speed >= 1000 && speed <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed RPM bounded 1000-3600 at 2900");
}

#[test]
fn test_side_channel_pump_power_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "power_x10 >= 1 && power_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "power_x10 == 75"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "power_x10 >= 1 && power_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power x10 kW bounded 1-500 at 7.5 kW");
}

#[test]
fn test_side_channel_pump_npsh_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("npsh_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "npsh_x10 >= 1 && npsh_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "npsh_x10 == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "npsh_x10 >= 1 && npsh_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NPSH required x10 m bounded 1-100 at 2.0 m");
}

#[test]
fn test_side_channel_pump_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "stages >= 1 && stages <= 12",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "stages == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "stages >= 1 && stages <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of pump stages bounded 1-12 at 4");
}

#[test]
fn test_side_channel_pump_impeller_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "enum",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "material >= 1 && material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impeller material 1=bronze 2=stainless 3=cast-iron within 1-3",
    );
}

#[test]
fn test_side_channel_pump_shaft_seal_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "enum",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("bounded", "seal >= 1 && seal <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shaft seal type 1=mechanical 2=packing 3=sealless within 1-3",
    );
}

#[test]
fn test_side_channel_pump_mounting_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mounting", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "enum",
        "mounting == 1 || mounting == 2 || mounting == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "mounting >= 1 && mounting <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mounting type 1=horizontal 2=vertical 3=close-coupled within 1-3",
    );
}

#[test]
fn test_side_channel_pump_self_priming_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("self_priming", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag", "self_priming == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "active",
        "if self_priming == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "self-priming boolean flag active when set to 1");
}
