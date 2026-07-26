// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Airflow rate scaled by 10 (units: x10 m^3/h).
/// Valid range: 0 < flow_x10 < 500000 (i.e., 0 to 50000 m^3/h).
#[test]
fn test_cross_flow_fan_airflow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 > 0 && flow_x10 < 500000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_positive",
        "flow_x10 >= 1 && flow_x10 <= 499999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scaled airflow rate in valid range implies tight bounds",
    );
}

/// Static pressure scaled by 10 (units: x10 Pa).
/// Valid range: 0 < press_x10 < 20000 (i.e., 0 to 2000 Pa).
#[test]
fn test_cross_flow_fan_static_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 > 0 && press_x10 < 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_positive",
        "press_x10 >= 1 && press_x10 <= 19999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scaled static pressure in valid range implies tight bounds",
    );
}

/// Impeller length scaled by 10 (units: x10 mm).
/// Valid range: 0 < len_x10 < 50000 (i.e., 0 to 5000 mm).
#[test]
fn test_cross_flow_fan_impeller_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("len_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "len_range",
        "len_x10 > 0 && len_x10 < 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "len_positive",
        "len_x10 >= 1 && len_x10 <= 49999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scaled impeller length in valid range implies tight bounds",
    );
}

/// Impeller diameter scaled by 10 (units: x10 mm).
/// Valid range: 0 < diam_x10 < 10000 (i.e., 0 to 1000 mm).
#[test]
fn test_cross_flow_fan_impeller_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diam_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diam_range",
        "diam_x10 > 0 && diam_x10 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diam_positive",
        "diam_x10 >= 1 && diam_x10 <= 9999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scaled impeller diameter in valid range implies tight bounds",
    );
}

/// Rotation speed bounded between 100 and 5000 RPM.
#[test]
fn test_cross_flow_fan_rotation_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 100 && rpm <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_in_bounds",
        "rpm > 0 && rpm < 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotation speed in [100, 5000] RPM is positive and below 10000",
    );
}

/// Number of blades bounded between 10 and 60.
#[test]
fn test_cross_flow_fan_blade_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blades", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "blade_range",
        "blades >= 10 && blades <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "blades_positive",
        "blades > 0 && blades <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "blade count in [10, 60] is positive and within 100",
    );
}

/// Blade curvature type: 1=forward-curved, 2=straight, 3=backward-inclined.
#[test]
fn test_cross_flow_fan_blade_curvature_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curve", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curve_type",
        "curve == 1 || curve == 2 || curve == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "curve_in_range",
        "curve >= 1 && curve <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "blade curvature disjunction implies range [1, 3]");
}

/// Stabilizer type: 1=vortex-wall, 2=rear-wall, 3=guide-vane.
#[test]
fn test_cross_flow_fan_stabilizer_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stab", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stab_type",
        "stab == 1 || stab == 2 || stab == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stab_in_range",
        "stab >= 1 && stab <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stabilizer type disjunction implies range [1, 3]");
}

/// Application type: 1=air-curtain, 2=HVAC, 3=electronics-cooling.
#[test]
fn test_cross_flow_fan_application_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("app", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "app_type",
        "app == 1 || app == 2 || app == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "app_in_range",
        "app >= 1 && app <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "application type disjunction implies range [1, 3]");
}

/// Automatic airflow balancing flag modeled as i32: 0=disabled, 1=enabled.
#[test]
fn test_cross_flow_fan_auto_balance_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_bal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_bool",
        "auto_bal == 0 || auto_bal == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded",
        "auto_bal >= 0 && auto_bal <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boolean flag as i32 is bounded to [0, 1]");
}
