// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_power_quality_voltage_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_voltage_range",
        "voltage >= 50 && voltage <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_voltage_bounded",
        "voltage >= 50 && voltage <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage RMS bounded 50-1000 V");
}

#[test]
fn test_power_quality_current_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_current_range",
        "current >= 1 && current <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_current_bounded",
        "current >= 1 && current <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "current bounded 1-10000 amps");
}

#[test]
fn test_power_quality_harmonic_order_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("order", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_order_range",
        "order >= 1 && order <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_order_bounded",
        "order >= 1 && order <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "harmonic order bounded 1-50");
}

#[test]
fn test_power_quality_thd_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thd_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_thd_range",
        "thd_x100 >= 0 && thd_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_thd_bounded",
        "thd_x100 >= 0 && thd_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "THD x100 bounded 0-10000 in 0.01 percent");
}

#[test]
fn test_power_quality_frequency_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_freq_range",
        "freq_x100 >= 4500 && freq_x100 <= 6500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_freq_bounded",
        "freq_x100 >= 4500 && freq_x100 <= 6500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency x100 bounded 4500-6500 in 0.01 Hz");
}

#[test]
fn test_power_quality_measurement_class_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_mc_valid",
        "mc == 1 || mc == 2 || mc == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_mc_three_way",
        "mc == 1 || mc == 2 || mc == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement class three-way 1=class-A 2=class-S 3=class-B",
    );
}

#[test]
fn test_power_quality_connection_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ct", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_ct_valid",
        "ct == 1 || ct == 2 || ct == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_ct_three_way",
        "ct == 1 || ct == 2 || ct == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "connection type three-way 1=single-phase 2=three-phase-wye 3=three-phase-delta",
    );
}

#[test]
fn test_power_quality_standard_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("std", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_std_valid",
        "std == 1 || std == 2 || std == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_std_three_way",
        "std == 1 || std == 2 || std == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "standard three-way 1=IEC-61000 2=IEEE-519 3=EN-50160",
    );
}

#[test]
fn test_power_quality_auto_event_capture_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_flag_bool",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_flag_boolean",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto event capture flag boolean 0 or 1");
}

#[test]
fn test_power_quality_sampling_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_rate_range",
        "rate >= 1000 && rate <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_rate_bounded",
        "rate >= 1000 && rate <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sampling rate bounded 1000-1000000 samples per sec",
    );
}
