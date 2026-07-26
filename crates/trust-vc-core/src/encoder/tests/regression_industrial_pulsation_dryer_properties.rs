// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_pulsation_dryer_pulse_frequency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pulse_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pf_a",
        "pulse_x10 >= 1 && pulse_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pf_c",
        "pulse_x10 >= 1 && pulse_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pulse frequency x10 in [1, 500] representing 0.1-50.0 Hz",
    );
}

#[test]
fn test_pulsation_dryer_air_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_a",
        "air_temp >= 150 && air_temp <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_c",
        "air_temp >= 150 && air_temp <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air temp offset+100 in [150, 600] representing 50-500 C",
    );
}

#[test]
fn test_pulsation_dryer_pulse_amplitude_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("amp_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pa_a",
        "amp_x100 >= 100 && amp_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pa_c",
        "amp_x100 >= 100 && amp_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pulse amplitude x100 in [100, 10000] representing 1.00-100.00%",
    );
}

#[test]
fn test_pulsation_dryer_duty_cycle_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("duty_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dc_a",
        "duty_x100 >= 1000 && duty_x100 <= 9000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dc_c",
        "duty_x100 >= 1000 && duty_x100 <= 9000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "duty cycle x100 in [1000, 9000] representing 10.00-90.00%",
    );
}

#[test]
fn test_pulsation_dryer_bed_height_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bed_mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bh_a",
        "bed_mm >= 10 && bed_mm <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bh_c",
        "bed_mm >= 10 && bed_mm <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bed height in [10, 1000] mm");
}

#[test]
fn test_pulsation_dryer_pressure_drop_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dp_pa", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "dp_pa >= 50 && dp_pa <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "dp_pa >= 50 && dp_pa <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure drop in [50, 10000] Pa");
}

#[test]
fn test_pulsation_dryer_valve_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vt_a",
        "valve == 1 || valve == 2 || valve == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("vt_c", "valve >= 1 && valve <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "valve type 3-way (butterfly/rotary/solenoid)");
}

#[test]
fn test_pulsation_dryer_distributor_plate_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pl_a",
        "plate == 1 || plate == 2 || plate == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("pl_c", "plate >= 1 && plate <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "distributor plate 3-way (perforated/nozzle/bubble-cap)",
    );
}

#[test]
fn test_pulsation_dryer_pulse_waveform_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("waveform", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wf_a",
        "waveform == 1 || waveform == 2 || waveform == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wf_c",
        "waveform >= 1 && waveform <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pulse waveform 3-way (square/sinusoidal/sawtooth)");
}

#[test]
fn test_pulsation_dryer_exhaust_heat_recovery_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "exhaust heat recovery flag is boolean (0 or 1)");
}
