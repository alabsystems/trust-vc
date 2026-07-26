// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_centrifugal_fan_airflow_scaled_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 > 0 && flow_x10 < 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert("flow_positive", "flow_x10 >= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "airflow scaled x10 m3/h must be positive");
}

#[test]
fn test_centrifugal_fan_static_pressure_scaled_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 > 0 && press_x10 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert("press_positive", "press_x10 >= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "static pressure scaled x10 Pa must be positive");
}

#[test]
fn test_centrifugal_fan_impeller_diameter_scaled_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diam_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diam_range",
        "diam_x10 > 0 && diam_x10 < 50000",
    ));
    ctx.push_obligation(ProofObligation::assert("diam_positive", "diam_x10 >= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller diameter scaled x10 mm must be positive");
}

#[test]
fn test_centrifugal_fan_rotation_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 100 && rpm <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_positive",
        "rpm > 0 && rpm <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotation speed bounded 100-10000 RPM implies positive and within limit",
    );
}

#[test]
fn test_centrifugal_fan_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_kw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power_kw >= 1 && power_kw <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_positive",
        "power_kw > 0 && power_kw <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motor power bounded 1-5000 kW implies positive and within limit",
    );
}

#[test]
fn test_centrifugal_fan_blade_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blades", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "blade_range",
        "blades >= 4 && blades <= 64",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "blade_positive",
        "blades > 0 && blades <= 64",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "blade count bounded 4-64 implies positive and within limit",
    );
}

#[test]
fn test_centrifugal_fan_blade_type_disjunction() {
    // 1=forward-curved, 2=backward-curved, 3=radial
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blade", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "blade_type",
        "blade == 1 || blade == 2 || blade == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "blade_valid",
        "blade >= 1 && blade <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "blade type 1/2/3 (forward/backward/radial) implies in [1,3]",
    );
}

#[test]
fn test_centrifugal_fan_housing_type_disjunction() {
    // 1=scroll, 2=inline, 3=plenum
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("housing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "housing_type",
        "housing == 1 || housing == 2 || housing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "housing_valid",
        "housing >= 1 && housing <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "housing type 1/2/3 (scroll/inline/plenum) implies in [1,3]",
    );
}

#[test]
fn test_centrifugal_fan_control_method_disjunction() {
    // 1=VFD, 2=inlet-vane, 3=damper
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ctrl_type",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ctrl_valid",
        "ctrl >= 1 && ctrl <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "control method 1/2/3 (VFD/inlet-vane/damper) implies in [1,3]",
    );
}

#[test]
fn test_centrifugal_fan_surge_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("surge_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "surge_bool",
        "surge_flag == 0 || surge_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "surge_bounded",
        "surge_flag >= 0 && surge_flag <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "surge protection flag is boolean (0 or 1) implies in [0,1]",
    );
}
