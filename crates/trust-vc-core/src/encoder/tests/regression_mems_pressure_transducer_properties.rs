// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_pressure_range_kpa() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_kpa", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range_val", "range_kpa == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "range_kpa >= 1 && range_kpa <= 70000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS pressure: range 1000 kPa in [1, 70000]");
}

#[test]
fn test_accuracy_x100_percent_fs() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("acc_val", "accuracy_x100 == 25"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "accuracy_x100 >= 1 && accuracy_x100 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MEMS pressure: accuracy 0.25% FS (25 x100) in [1, 100]",
    );
}

#[test]
fn test_sensing_element_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensing_element", i32_ty());
    // 1=piezoresistive, 2=capacitive, 3=resonant
    ctx.push_obligation(ProofObligation::assume("se_val", "sensing_element == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "sensing_element == 1 || sensing_element == 2 || sensing_element == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MEMS pressure: sensing element piezoresistive (1) in {1,2,3}",
    );
}

#[test]
fn test_pressure_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_type", i32_ty());
    // 1=absolute, 2=gauge, 3=differential, 4=sealed gauge
    ctx.push_obligation(ProofObligation::assume("pt_val", "pressure_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "pressure_type == 1 || pressure_type == 2 || pressure_type == 3 || pressure_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS pressure: type absolute (1) in {1,2,3,4}");
}

#[test]
fn test_output_signal_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_signal", i32_ty());
    // 1=4-20mA, 2=0-5V, 3=0-10V, 4=I2C
    ctx.push_obligation(ProofObligation::assume("os_val", "output_signal == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_signal",
        "output_signal == 1 || output_signal == 2 || output_signal == 3 || output_signal == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS pressure: output 4-20mA (1) in {1,2,3,4}");
}

#[test]
fn test_burst_pressure_kpa() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("burst_kpa", u32_ty());
    ctx.push_obligation(ProofObligation::assume("burst_val", "burst_kpa == 4000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "burst_kpa >= 500 && burst_kpa <= 200000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS pressure: burst 4000 kPa in [500, 200000]");
}

#[test]
fn test_response_time_us() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("response_us", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rt_val", "response_us == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "response_us >= 1 && response_us <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS pressure: response 100 us in [1, 10000]");
}

#[test]
fn test_package_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("package", i32_ty());
    // 1=DIP, 2=SMD, 3=TO-can
    ctx.push_obligation(ProofObligation::assume("pkg_val", "package == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_package",
        "package == 1 || package == 2 || package == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MEMS pressure: package DIP (1) in {1,2,3}");
}

#[test]
fn test_operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    // Offset +500: 25C -> 525, -40C -> 460, 125C -> 625
    ctx.push_obligation(ProofObligation::assume("to_val", "temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "temp_offset >= 460 && temp_offset <= 625",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MEMS pressure: temp 25C (offset 525) in [460, 625]",
    );
}

#[test]
fn test_overpressure_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.declare_var_typed("protected", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "prot_def",
        "protected == if flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("enabled", "protected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MEMS pressure: overpressure protection enabled (flag=1)",
    );
}
