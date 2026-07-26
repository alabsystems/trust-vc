// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_phase_angle_meter_angle_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "angle_x100 >= 0 && angle_x100 <= 36000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "angle_x100 >= 0 && angle_x100 <= 36000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase angle meter: angle x100 degrees (0-360.00 deg) bounded",
    );
}

#[test]
fn test_phase_angle_meter_frequency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "freq_x10 >= 1 && freq_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "freq_x10 >= 1 && freq_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase angle meter: frequency x10 Hz (0.1-1000.0 Hz) bounded",
    );
}

#[test]
fn test_phase_angle_meter_voltage_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volt_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "volt_x100 >= 1 && volt_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "volt_x100 >= 1 && volt_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase angle meter: voltage x100 V (0.01-1000.00 V) bounded",
    );
}

#[test]
fn test_phase_angle_meter_current_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "curr_x1000 >= 1 && curr_x1000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "curr_x1000 >= 1 && curr_x1000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase angle meter: current x1000 A (0.001-100.000 A) bounded",
    );
}

#[test]
fn test_phase_angle_meter_resolution_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "res_x10000 >= 1 && res_x10000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "res_x10000 >= 1 && res_x10000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase angle meter: resolution x10000 degrees (0.0001-0.1000 deg) bounded",
    );
}

#[test]
fn test_phase_angle_meter_power_factor_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pf_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "pf_x10000 >= 0 && pf_x10000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "pf_x10000 >= 0 && pf_x10000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase angle meter: power factor x10000 (0.0000-1.0000) bounded",
    );
}

#[test]
fn test_phase_angle_meter_measurement_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase angle meter: method 1=zero-crossing, 2=FFT, 3=correlation",
    );
}

#[test]
fn test_phase_angle_meter_input_coupling_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coupling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "coupling == 1 || coupling == 2 || coupling == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "coupling == 1 || coupling == 2 || coupling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase angle meter: coupling 1=direct, 2=CT-clamp, 3=differential",
    );
}

#[test]
fn test_phase_angle_meter_display_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase angle meter: display 1=numeric, 2=phasor, 3=waveform",
    );
}

#[test]
fn test_phase_angle_meter_auto_range_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bounds",
        "auto_range == 0 || auto_range == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "auto_range == 0 || auto_range == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "precision phase angle meter: auto range boolean 0 or 1",
    );
}
