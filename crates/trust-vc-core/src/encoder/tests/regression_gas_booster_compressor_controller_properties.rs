// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_gas_booster_inlet_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inlet_pressure_range",
        "inlet_pressure >= 1 && inlet_pressure <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_pressure_valid",
        "inlet_pressure >= 1 && inlet_pressure <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet pressure must be within 1-500 bar");
}

#[test]
fn test_gas_booster_outlet_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("outlet_pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "outlet_pressure_range",
        "outlet_pressure >= 10 && outlet_pressure <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "outlet_pressure_valid",
        "outlet_pressure >= 10 && outlet_pressure <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "outlet pressure must be within 10-3000 bar");
}

#[test]
fn test_gas_booster_compression_ratio_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("compression_ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "compression_ratio_x10_range",
        "compression_ratio_x10 >= 10 && compression_ratio_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "compression_ratio_x10_valid",
        "compression_ratio_x10 >= 10 && compression_ratio_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compression ratio x10 must be within 10-200 (1.0-20.0)",
    );
}

#[test]
fn test_gas_booster_cycle_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycle_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cycle_rate_range",
        "cycle_rate >= 1 && cycle_rate <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cycle_rate_valid",
        "cycle_rate >= 1 && cycle_rate <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cycle rate must be within 1-60 cycles/min");
}

#[test]
fn test_gas_booster_gas_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_temp_offset100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gas_temp_offset100_range",
        "gas_temp_offset100 >= 50 && gas_temp_offset100 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gas_temp_offset100_valid",
        "gas_temp_offset100 >= 50 && gas_temp_offset100 <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gas temperature offset+100 must be within 50-300 (-50 to 200 C)",
    );
}

#[test]
fn test_gas_booster_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_rate_x10_range",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_rate_x10_valid",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate x10 must be within 1-5000 (0.1-500.0 Nm3/h)",
    );
}

#[test]
fn test_gas_booster_drive_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drive_type_range",
        "drive_type >= 1 && drive_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drive_type_valid",
        "drive_type >= 1 && drive_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive type must be 1=pneumatic, 2=hydraulic, or 3=electric",
    );
}

#[test]
fn test_gas_booster_sealing_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sealing_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sealing_type_range",
        "sealing_type >= 1 && sealing_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sealing_type_valid",
        "sealing_type >= 1 && sealing_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sealing type must be 1=piston-ring, 2=diaphragm, or 3=metal-bellows",
    );
}

#[test]
fn test_gas_booster_gas_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gas_type_range",
        "gas_type >= 1 && gas_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gas_type_valid",
        "gas_type >= 1 && gas_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gas type must be 1=nitrogen, 2=hydrogen, or 3=natural-gas",
    );
}

#[test]
fn test_gas_booster_auto_pressure_regulation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_pressure_regulation", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_pressure_regulation_range",
        "auto_pressure_regulation >= 0 && auto_pressure_regulation <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_pressure_regulation_valid",
        "auto_pressure_regulation >= 0 && auto_pressure_regulation <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto pressure regulation flag must be 0=disabled or 1=enabled",
    );
}
