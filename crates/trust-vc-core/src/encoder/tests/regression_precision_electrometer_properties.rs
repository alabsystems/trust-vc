// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Precision electrometer property verification.
// Models key instrument parameters: input impedance, current sensitivity,
// voltage range, charge measurement range, reading rate, input connector type,
// measurement function, guard mode, accuracy (x1000 scaling), and auto zero flag.

#[test]
fn test_input_impedance_bounded() {
    // Input impedance in teraohms (1 to 200 TOhm)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impedance_tohm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "impedance_bounds",
        "impedance_tohm >= 1 && impedance_tohm <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "impedance_positive",
        "impedance_tohm >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "impedance_upper",
        "impedance_tohm <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input impedance bounded in [1, 200] TOhm");
}

#[test]
fn test_current_sensitivity_bounded() {
    // Current sensitivity in femtoamperes (1 to 100 fA)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensitivity_fa", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sensitivity_bounds",
        "sensitivity_fa >= 1 && sensitivity_fa <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sensitivity_positive",
        "sensitivity_fa >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sensitivity_upper",
        "sensitivity_fa <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "current sensitivity bounded in [1, 100] fA");
}

#[test]
fn test_voltage_range_bounded() {
    // Voltage range in volts (1 to 1000 V)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_v", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_bounds",
        "voltage_v >= 1 && voltage_v <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_positive",
        "voltage_v >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_upper",
        "voltage_v <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage range bounded in [1, 1000] V");
}

#[test]
fn test_charge_measurement_range_bounded() {
    // Charge measurement range in picocoulombs (1 to 10000 pC)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("charge_pc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "charge_bounds",
        "charge_pc >= 1 && charge_pc <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert("charge_positive", "charge_pc >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "charge_upper",
        "charge_pc <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "charge measurement range bounded in [1, 10000] pC");
}

#[test]
fn test_reading_rate_bounded() {
    // Reading rate in readings per second (1 to 2000)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_bounds",
        "rate >= 1 && rate <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert("rate_positive", "rate >= 1"));
    ctx.push_obligation(ProofObligation::assert("rate_upper", "rate <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reading rate bounded in [1, 2000] readings/s");
}

#[test]
fn test_input_connector_type_three_way_disjunction() {
    // Input connector type: 1=BNC, 2=triax, 3=banana
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("connector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "connector_valid",
        "connector == 1 || connector == 2 || connector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("connector_lower", "connector >= 1"));
    ctx.push_obligation(ProofObligation::assert("connector_upper", "connector <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "input connector is one of BNC(1), triax(2), banana(3)",
    );
}

#[test]
fn test_measurement_function_three_way_disjunction() {
    // Measurement function: 1=voltage, 2=current, 3=charge
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("function", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "function_valid",
        "function == 1 || function == 2 || function == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("function_lower", "function >= 1"));
    ctx.push_obligation(ProofObligation::assert("function_upper", "function <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement function is one of voltage(1), current(2), charge(3)",
    );
}

#[test]
fn test_guard_mode_three_way_disjunction() {
    // Guard mode: 1=cable, 2=driven, 3=floating
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("guard", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "guard_valid",
        "guard == 1 || guard == 2 || guard == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("guard_lower", "guard >= 1"));
    ctx.push_obligation(ProofObligation::assert("guard_upper", "guard <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "guard mode is one of cable(1), driven(2), floating(3)",
    );
}

#[test]
fn test_accuracy_scaled_bounded() {
    // Accuracy encoded as x1000 percentage (1 = 0.001%, 500 = 0.500%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_bounds",
        "accuracy_x1000 >= 1 && accuracy_x1000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_positive",
        "accuracy_x1000 >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_upper",
        "accuracy_x1000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy x1000 bounded in [1, 500] (0.001% to 0.500%)",
    );
}

#[test]
fn test_auto_zero_boolean_flag() {
    // Auto zero enable: i32 flag where 1=enabled, 0=disabled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_zero", i32_ty());
    ctx.declare_var_typed("active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid",
        "auto_zero == 0 || auto_zero == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("auto_zero_on", "auto_zero == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "active_def",
        "active == if auto_zero == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "active_when_enabled",
        "active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto zero flag: enabled(1) produces active=1");
}
