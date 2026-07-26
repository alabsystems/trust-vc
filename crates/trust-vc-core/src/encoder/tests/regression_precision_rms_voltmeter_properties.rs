// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Voltage range scaled x1000: 1..1500000 represents 0.001V to 1500V.
#[test]
fn test_rms_voltmeter_voltage_range_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range_a",
        "voltage >= 1 && voltage <= 1500000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_range_c",
        "voltage >= 1 && voltage <= 1500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage x1000 in [1, 1500000] for 0.001V-1500V");
}

/// Frequency range scaled x10: 1..100000000 represents 0.1Hz to 10MHz.
#[test]
fn test_rms_voltmeter_frequency_range_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frequency", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "frequency_range_a",
        "frequency >= 1 && frequency <= 100000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "frequency_range_c",
        "frequency >= 1 && frequency <= 100000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency x10 in [1, 100000000] for 0.1Hz-10MHz");
}

/// Accuracy scaled x10000: 1..500 represents 0.0001% to 0.05%.
#[test]
fn test_rms_voltmeter_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_range_a",
        "accuracy >= 1 && accuracy <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_range_c",
        "accuracy >= 1 && accuracy <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy x10000 in [1, 500] for 0.0001%-0.05%");
}

/// Crest factor scaled x100: 100..700 represents 1.0 to 7.0.
#[test]
fn test_rms_voltmeter_crest_factor_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("crest", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "crest_range_a",
        "crest >= 100 && crest <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "crest_range_c",
        "crest >= 100 && crest <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crest factor x100 in [100, 700] for 1.0-7.0");
}

/// Input impedance scaled x10: 1..100000 represents 0.1 MOhm to 10000 MOhm.
#[test]
fn test_rms_voltmeter_input_impedance_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impedance", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "impedance_range_a",
        "impedance >= 1 && impedance <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "impedance_range_c",
        "impedance >= 1 && impedance <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "input impedance x10 in [1, 100000] for 0.1-10000 MOhm",
    );
}

/// Bandwidth scaled x10: 1..100000000 represents 0.1Hz to 10MHz.
#[test]
fn test_rms_voltmeter_bandwidth_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bandwidth", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bandwidth_range_a",
        "bandwidth >= 1 && bandwidth <= 100000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bandwidth_range_c",
        "bandwidth >= 1 && bandwidth <= 100000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bandwidth x10 in [1, 100000000] for 0.1Hz-10MHz");
}

/// Detector mode: 1=average, 2=peak, 3=true-rms.
#[test]
fn test_rms_voltmeter_detector_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detector_mode_a",
        "detector >= 1 && detector <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detector_mode_c",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector mode is average(1), peak(2), or true-rms(3)",
    );
}

/// Coupling mode: 1=AC, 2=DC, 3=AC+DC.
#[test]
fn test_rms_voltmeter_coupling_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coupling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "coupling_mode_a",
        "coupling >= 1 && coupling <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "coupling_mode_c",
        "coupling == 1 || coupling == 2 || coupling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "coupling mode is AC(1), DC(2), or AC+DC(3)");
}

/// Measurement range: 1=auto, 2=manual, 3=fixed.
#[test]
fn test_rms_voltmeter_measurement_range_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mrange", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mrange_mode_a",
        "mrange >= 1 && mrange <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mrange_mode_c",
        "mrange == 1 || mrange == 2 || mrange == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement range is auto(1), manual(2), or fixed(3)",
    );
}

/// Auto-zero flag: must be exactly 0 or 1.
#[test]
fn test_rms_voltmeter_auto_zero_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_binary_a",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_binary_c",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-zero flag is boolean (0 or 1)");
}
