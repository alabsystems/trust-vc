// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_pressure_range_scaled() {
    // Pressure in ×10 Pa (0.1 Pa resolution): 0 to 10_000_000 (0 to 1 MPa)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "pressure_x10 == 1013250")); // 101325.0 Pa (1 atm)
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if pressure_x10 >= 0 && pressure_x10 <= 10000000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "manometer: 101325.0 Pa within 0-1MPa range");
}

#[test]
fn test_accuracy_scaled() {
    // Accuracy in ×100 %FS (0.01% resolution): e.g., 5 = 0.05% FS
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x100", u32_ty());
    ctx.declare_var_typed("acceptable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "accuracy_x100 == 5")); // 0.05% FS
    ctx.push_obligation(ProofObligation::assume(
        "acc_def",
        "acceptable == if accuracy_x100 >= 1 && accuracy_x100 <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "manometer: 0.05% FS accuracy within 0.01-1.00% FS");
}

#[test]
fn test_resolution_scaled() {
    // Resolution in ×1000 Pa (0.001 Pa resolution): e.g., 1 = 0.001 Pa
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x1000", u32_ty());
    ctx.declare_var_typed("within_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "resolution_x1000 == 10")); // 0.010 Pa
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_spec == if resolution_x1000 >= 1 && resolution_x1000 <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "manometer: 0.010 Pa resolution within 0.001-1.000 Pa",
    );
}

#[test]
fn test_display_digits_bounded() {
    // Display digits: 4 to 7 digits
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("digits", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "digits == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if digits >= 4 && digits <= 7 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "manometer: 5 display digits within 4-7 range");
}

#[test]
fn test_sample_rate_bounded() {
    // Sample rate: 1 to 1000 Hz
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_rate_hz", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate_hz == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if sample_rate_hz >= 1 && sample_rate_hz <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "manometer: 100 Hz sample rate within 1-1000 Hz");
}

#[test]
fn test_pressure_type_disjunction() {
    // Pressure type: 1=gauge, 2=absolute, 3=differential
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pt", "pressure_type == 2")); // absolute
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if pressure_type == 1 || pressure_type == 2 || pressure_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "manometer: absolute (2) is valid pressure type");
}

#[test]
fn test_sensor_type_disjunction() {
    // Sensor type: 1=piezoresistive, 2=capacitive, 3=resonant
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("st", "sensor_type == 1")); // piezoresistive
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if sensor_type == 1 || sensor_type == 2 || sensor_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "manometer: piezoresistive (1) is valid sensor type",
    );
}

#[test]
fn test_operating_temp_offset() {
    // Operating temp with +500 offset: -40C to +85C → 460 to 585
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "temp_offset == 525")); // 25C + 500 offset
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_offset >= 460 && temp_offset <= 585 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "manometer: 25C (offset 525) within -40C to 85C range",
    );
}

#[test]
fn test_media_compatibility_disjunction() {
    // Media compatibility: 1=gas, 2=liquid, 3=corrosive
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("media_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mt", "media_type == 3")); // corrosive
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if media_type == 1 || media_type == 2 || media_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "manometer: corrosive (3) is valid media type");
}

#[test]
fn test_data_logging_flag() {
    // Data logging: boolean flag (i32, 1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("logging_enabled", i32_ty());
    ctx.declare_var_typed("log_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume("le", "logging_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "la_def",
        "log_active == if logging_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "log_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "manometer: data logging enabled");
}
