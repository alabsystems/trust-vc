// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_precision_thermistor_meter_resistance_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resistance_ohm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // NTC thermistor resistance: 100 to 1000000 ohms
    ctx.push_obligation(ProofObligation::assume("r", "resistance_ohm == 10000")); // 10k NTC at 25C
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if resistance_ohm >= 100 && resistance_ohm <= 1000000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermistor: 10000 ohm in [100, 1000000]");
}

#[test]
fn test_precision_thermistor_meter_temperature_range_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Offset +500: -40C = 460, +150C = 650. Measuring 25C = 525.
    ctx.push_obligation(ProofObligation::assume("t", "temp_offset == 525")); // 25C
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_offset >= 460 && temp_offset <= 650 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thermistor temp: 525 (25C) in [460 (-40C), 650 (150C)]",
    );
}

#[test]
fn test_precision_thermistor_meter_accuracy_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x100", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    // Accuracy scaled x100: 10 = 0.10C, max acceptable = 50 (0.50C)
    ctx.push_obligation(ProofObligation::assume("a", "accuracy_x100 == 10")); // 0.10C
    ctx.push_obligation(ProofObligation::assume(
        "acc_def",
        "acceptable == if accuracy_x100 >= 1 && accuracy_x100 <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermistor accuracy: 10 (0.10C) in [1, 50]");
}

#[test]
fn test_precision_thermistor_meter_beta_value_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("beta_k", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // Beta coefficient for NTC: typically 2000K to 5000K
    ctx.push_obligation(ProofObligation::assume("b", "beta_k == 3950")); // common 10k NTC beta
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if beta_k >= 2000 && beta_k <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermistor beta: 3950K in [2000, 5000]");
}

#[test]
fn test_precision_thermistor_meter_excitation_current_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("excitation_x1000", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // Excitation current scaled x1000 uA: 100 = 0.100 uA, range 10 to 5000 (0.010 to 5.000 uA)
    ctx.push_obligation(ProofObligation::assume("e", "excitation_x1000 == 100")); // 0.100 uA
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if excitation_x1000 >= 10 && excitation_x1000 <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thermistor excitation: 100 (0.100 uA) in [10, 5000]",
    );
}

#[test]
fn test_precision_thermistor_meter_sensor_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // 1=NTC, 2=PTC, 3=RTD
    ctx.push_obligation(ProofObligation::assume("st", "sensor_type == 1")); // NTC
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if sensor_type == 1 || sensor_type == 2 || sensor_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermistor sensor type: 1 (NTC) in {1,2,3}");
}

#[test]
fn test_precision_thermistor_meter_wire_configuration_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wire_config", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // 1=two-wire, 2=three-wire, 3=four-wire
    ctx.push_obligation(ProofObligation::assume("wc", "wire_config == 3")); // four-wire (best accuracy)
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if wire_config == 1 || wire_config == 2 || wire_config == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermistor wire: 3 (four-wire) in {1,2,3}");
}

#[test]
fn test_precision_thermistor_meter_measurement_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // Measurement channels: 1 to 16
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if channels >= 1 && channels <= 16 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermistor channels: 8 in [1, 16]");
}

#[test]
fn test_precision_thermistor_meter_self_heating_coefficient_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("self_heat_x1000", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    // Self-heating coefficient scaled x1000 mK/mW: 500 = 0.500 mK/mW, max 2000 (2.000 mK/mW)
    ctx.push_obligation(ProofObligation::assume("sh", "self_heat_x1000 == 500")); // 0.500 mK/mW
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if self_heat_x1000 >= 1 && self_heat_x1000 <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thermistor self-heating: 500 (0.500 mK/mW) in [1, 2000]",
    );
}

#[test]
fn test_precision_thermistor_meter_data_logging_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("logging_enabled", i32_ty());
    ctx.declare_var_typed("is_active", i32_ty());
    // Boolean flag: 1 = enabled, 0 = disabled
    ctx.push_obligation(ProofObligation::assume("le", "logging_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "is_active == if logging_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "is_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "thermistor data logging: enabled flag == 1");
}
