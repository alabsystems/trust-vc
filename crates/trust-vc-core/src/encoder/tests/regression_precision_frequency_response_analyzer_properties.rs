// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Precision Frequency Response Analyzer (FRA) property regression tests

use super::*;

#[test]
fn test_fra_frequency_range_mhz_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_mhz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "freq_mhz >= 1 && freq_mhz <= 120000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "freq_mhz == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "freq_mhz >= 1 && freq_mhz <= 120000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FRA frequency range bounded 1-120000 MHz with value 30000 MHz",
    );
}

#[test]
fn test_fra_dynamic_range_db_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dynamic_range_db", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "dynamic_range_db >= 40 && dynamic_range_db <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "dynamic_range_db == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "dynamic_range_db >= 40 && dynamic_range_db <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FRA dynamic range bounded 40-200 dB with value 150 dB",
    );
}

#[test]
fn test_fra_amplitude_accuracy_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("amp_acc_x1000", i32_ty());
    // Amplitude accuracy x1000 dB (0.001 dB precision): 50 = 0.050 dB
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "amp_acc_x1000 >= 1 && amp_acc_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "amp_acc_x1000 == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "amp_acc_x1000 >= 1 && amp_acc_x1000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FRA amplitude accuracy x1000 bounded 1-1000 with value 50 (0.050 dB)",
    );
}

#[test]
fn test_fra_phase_accuracy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase_acc_x100", i32_ty());
    // Phase accuracy x100 degrees (0.01 degree precision): 10 = 0.10 degrees
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "phase_acc_x100 >= 1 && phase_acc_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "phase_acc_x100 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "phase_acc_x100 >= 1 && phase_acc_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FRA phase accuracy x100 bounded 1-500 with value 10 (0.10 degrees)",
    );
}

#[test]
fn test_fra_number_of_points_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_points", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "num_points >= 1 && num_points <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "num_points == 10001"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "num_points >= 1 && num_points <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FRA number of points bounded 1-100000 with value 10001",
    );
}

#[test]
fn test_fra_if_bandwidth_hz_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("if_bw_hz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "if_bw_hz >= 1 && if_bw_hz <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "if_bw_hz == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "if_bw_hz >= 1 && if_bw_hz <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FRA IF bandwidth bounded 1-100000 Hz with value 100 Hz",
    );
}

#[test]
fn test_fra_source_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("src_type", i32_ty());
    // Source type: 1=swept-sine, 2=multi-tone, 3=chirp
    ctx.push_obligation(ProofObligation::assume("val", "src_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "src_type == 1 || src_type == 2 || src_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FRA source type disjunction 1=swept-sine 2=multi-tone 3=chirp",
    );
}

#[test]
fn test_fra_receiver_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rcv_type", i32_ty());
    // Receiver type: 1=narrowband, 2=wideband, 3=correlation
    ctx.push_obligation(ProofObligation::assume("val", "rcv_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "rcv_type == 1 || rcv_type == 2 || rcv_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FRA receiver type disjunction 1=narrowband 2=wideband 3=correlation",
    );
}

#[test]
fn test_fra_display_format_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_fmt", i32_ty());
    // Display format: 1=bode, 2=nyquist, 3=nichols
    ctx.push_obligation(ProofObligation::assume("val", "disp_fmt == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "disp_fmt == 1 || disp_fmt == 2 || disp_fmt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FRA display format disjunction 1=bode 2=nyquist 3=nichols",
    );
}

#[test]
fn test_fra_automatic_calibration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "auto_cal",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "FRA automatic calibration flag assumed 1 implies conditional equals 1",
    );
}
