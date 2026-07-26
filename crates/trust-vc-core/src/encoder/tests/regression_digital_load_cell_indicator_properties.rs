// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Digital load cell weighing indicator property verification.
// Encodes key parameters of an industrial weighing system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Max capacity (kg) — weighing capacity bounded [1, 100000], value 5000.
#[test]
fn test_max_capacity_kg_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity_kg", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cap_val", "capacity_kg == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "cap_in_range",
        "capacity_kg >= 1 && capacity_kg <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max capacity 5000 kg within [1, 100000]");
}

/// Test 2: Resolution (divisions) — display divisions bounded [1000, 100000], value 10000.
#[test]
fn test_resolution_divisions_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("divisions", u32_ty());
    ctx.push_obligation(ProofObligation::assume("div_val", "divisions == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "div_in_range",
        "divisions >= 1000 && divisions <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 10000 divisions within [1000, 100000]");
}

/// Test 3: Accuracy class — 3-way disjunction (1=OIML class I, 2=class II, 3=class III).
#[test]
fn test_accuracy_class_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_class", u32_ty());
    ctx.push_obligation(ProofObligation::assume("acc_val", "acc_class == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "acc_valid",
        "acc_class == 1 || acc_class == 2 || acc_class == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy class II (2) is valid 3-way disjunction");
}

/// Test 4: ADC bit depth — 4-way non-sequential disjunction (16, 20, 24, 32).
#[test]
fn test_adc_bit_depth_non_sequential() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("adc_bits", u32_ty());
    ctx.declare_var_typed("valid_bits", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bits_val", "adc_bits == 24"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_bits == if adc_bits == 16 || adc_bits == 20 || adc_bits == 24 || adc_bits == 32 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_valid", "valid_bits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC bit depth 24 is valid in {16, 20, 24, 32}");
}

/// Test 5: Input channels — load cell count bounded [1, 16], value 4.
#[test]
fn test_input_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ch_val", "channels == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "ch_in_range",
        "channels >= 1 && channels <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input channels 4 load cells within [1, 16]");
}

/// Test 6: Excitation voltage (mV) — bridge drive bounded [5000, 15000], value 10000 (10V).
#[test]
fn test_excitation_voltage_mv_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("excitation_mv", u32_ty());
    ctx.push_obligation(ProofObligation::assume("exc_val", "excitation_mv == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "exc_in_range",
        "excitation_mv >= 5000 && excitation_mv <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "excitation voltage 10000 mV (10V) within [5000, 15000]",
    );
}

/// Test 7: Update rate (Hz) — display/output refresh bounded [1, 100], value 10.
#[test]
fn test_update_rate_hz_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_hz", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rate_val", "rate_hz == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "rate_in_range",
        "rate_hz >= 1 && rate_hz <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "update rate 10 Hz within [1, 100]");
}

/// Test 8: Communication interface — 4-way disjunction (1=RS232, 2=RS485, 3=USB, 4=Ethernet).
#[test]
fn test_communication_interface_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("comm_val", "comm == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "comm_valid",
        "comm == 1 || comm == 2 || comm == 3 || comm == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "communication RS485 (2) is valid 4-way disjunction",
    );
}

/// Test 9: Operating temperature with +500 offset (deg C) — value 525 (25 deg C).
/// Range: 460 (-40 deg C) to 570 (70 deg C).
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 525"));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "temp >= 460 && temp <= 570",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 25 deg C (offset 525) within [-40, 70] deg C",
    );
}

/// Test 10: Legal for trade — boolean flag using i32 (1 = certified, 0 = not certified).
#[test]
fn test_legal_for_trade_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lft_flag", i32_ty());
    ctx.declare_var_typed("sealed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lft_enabled", "lft_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sealed_def",
        "sealed == if lft_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_sealed", "sealed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "legal for trade enabled triggers sealed mode");
}
