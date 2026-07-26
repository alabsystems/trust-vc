// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Precision Gain-Phase Analyzer property regression tests

use super::*;

#[test]
fn test_gain_phase_frequency_range_khz_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_khz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "freq_khz >= 1 && freq_khz <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "freq_khz == 15000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "freq_khz >= 1 && freq_khz <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gain-phase frequency range bounded 1-100000 kHz with value 15000 kHz",
    );
}

#[test]
fn test_gain_phase_gain_accuracy_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gain_acc_x1000", i32_ty());
    // Gain accuracy x1000 dB (0.001 dB precision): 10 = 0.010 dB
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "gain_acc_x1000 >= 1 && gain_acc_x1000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "gain_acc_x1000 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "gain_acc_x1000 >= 1 && gain_acc_x1000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gain-phase gain accuracy x1000 bounded 1-500 with value 10 (0.010 dB)",
    );
}

#[test]
fn test_gain_phase_phase_accuracy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase_acc_x100", i32_ty());
    // Phase accuracy x100 degrees (0.01 degree precision): 5 = 0.05 degrees
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "phase_acc_x100 >= 1 && phase_acc_x100 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "phase_acc_x100 == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "phase_acc_x100 >= 1 && phase_acc_x100 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gain-phase phase accuracy x100 bounded 1-200 with value 5 (0.05 degrees)",
    );
}

#[test]
fn test_gain_phase_dynamic_range_db_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dynamic_range_db", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "dynamic_range_db >= 40 && dynamic_range_db <= 180",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "dynamic_range_db == 130"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "dynamic_range_db >= 40 && dynamic_range_db <= 180",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gain-phase dynamic range bounded 40-180 dB with value 130 dB",
    );
}

#[test]
fn test_gain_phase_input_impedance_ohms_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impedance_ohms", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "impedance_ohms >= 50 && impedance_ohms <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "impedance_ohms == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "impedance_ohms >= 50 && impedance_ohms <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gain-phase input impedance bounded 50-1000000 ohms with value 50 ohms",
    );
}

#[test]
fn test_gain_phase_number_of_test_ports_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_ports", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "num_ports >= 1 && num_ports <= 4",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "num_ports == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "num_ports >= 1 && num_ports <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gain-phase number of test ports bounded 1-4 with value 2",
    );
}

#[test]
fn test_gain_phase_measurement_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_mode", i32_ty());
    // Measurement mode: 1=transfer-function, 2=impedance, 3=admittance
    ctx.push_obligation(ProofObligation::assume("val", "meas_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "meas_mode == 1 || meas_mode == 2 || meas_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gain-phase measurement mode disjunction 1=transfer-function 2=impedance 3=admittance",
    );
}

#[test]
fn test_gain_phase_sweep_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sweep_type", i32_ty());
    // Sweep type: 1=linear, 2=logarithmic, 3=list
    ctx.push_obligation(ProofObligation::assume("val", "sweep_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "sweep_type == 1 || sweep_type == 2 || sweep_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gain-phase sweep type disjunction 1=linear 2=logarithmic 3=list",
    );
}

#[test]
fn test_gain_phase_source_waveform_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("src_wave", i32_ty());
    // Source waveform: 1=sine, 2=multitone, 3=swept-sine
    ctx.push_obligation(ProofObligation::assume("val", "src_wave == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "src_wave == 1 || src_wave == 2 || src_wave == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gain-phase source waveform disjunction 1=sine 2=multitone 3=swept-sine",
    );
}

#[test]
fn test_gain_phase_automatic_level_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "alc",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gain-phase automatic level control flag assumed 1 implies conditional equals 1",
    );
}
