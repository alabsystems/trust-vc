// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Start frequency in Hz must be bounded between 1 and 1000000.
#[test]
fn test_sweep_freq_analyzer_start_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("start_freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sf_a",
        "start_freq >= 1 && start_freq <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sf_c",
        "start_freq >= 1 && start_freq <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sweep frequency analyzer start frequency bounded 1-1000000 Hz",
    );
}

/// Stop frequency in Hz must be bounded between 100 and 10000000.
#[test]
fn test_sweep_freq_analyzer_stop_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stop_freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ef_a",
        "stop_freq >= 100 && stop_freq <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ef_c",
        "stop_freq >= 100 && stop_freq <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sweep frequency analyzer stop frequency bounded 100-10000000 Hz",
    );
}

/// Amplitude at x100 Vrms must be bounded between 1 and 2000.
#[test]
fn test_sweep_freq_analyzer_amplitude_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("amp_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "am_a",
        "amp_x100 >= 1 && amp_x100 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "am_c",
        "amp_x100 >= 1 && amp_x100 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sweep frequency analyzer amplitude x100 Vrms bounded 1-2000",
    );
}

/// Number of sweep points must be bounded between 50 and 10000.
#[test]
fn test_sweep_freq_analyzer_sweep_points_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("points", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sp_a",
        "points >= 50 && points <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sp_c",
        "points >= 50 && points <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sweep frequency analyzer sweep points bounded 50-10000",
    );
}

/// Input impedance at x10 ohms must be bounded between 1 and 100000.
#[test]
fn test_sweep_freq_analyzer_input_impedance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("imp_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ii_a",
        "imp_x10 >= 1 && imp_x10 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ii_c",
        "imp_x10 >= 1 && imp_x10 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sweep frequency analyzer input impedance x10 ohms bounded 1-100000",
    );
}

/// Dynamic range in dB must be bounded between 60 and 160.
#[test]
fn test_sweep_freq_analyzer_dynamic_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_db", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dr_a",
        "range_db >= 60 && range_db <= 160",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dr_c",
        "range_db >= 60 && range_db <= 160",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sweep frequency analyzer dynamic range bounded 60-160 dB",
    );
}

/// Measurement type must be one of: 1=impedance, 2=admittance, 3=transfer-function.
#[test]
fn test_sweep_freq_analyzer_measurement_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mtype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mt_a",
        "mtype == 1 || mtype == 2 || mtype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mt_c",
        "mtype == 1 || mtype == 2 || mtype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sweep frequency analyzer measurement type 1=impedance 2=admittance 3=transfer-function",
    );
}

/// Window function must be one of: 1=Hanning, 2=rectangular, 3=flat-top.
#[test]
fn test_sweep_freq_analyzer_window_function_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("window", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wf_a",
        "window == 1 || window == 2 || window == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wf_c",
        "window == 1 || window == 2 || window == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sweep frequency analyzer window function 1=Hanning 2=rectangular 3=flat-top",
    );
}

/// Test standard must be one of: 1=IEC60076, 2=IEEE-C57, 3=CIGRE.
#[test]
fn test_sweep_freq_analyzer_test_standard_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("standard", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ts_a",
        "standard == 1 || standard == 2 || standard == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ts_c",
        "standard == 1 || standard == 2 || standard == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sweep frequency analyzer test standard 1=IEC60076 2=IEEE-C57 3=CIGRE",
    );
}

/// Automatic resonance detection flag must be a boolean (0 or 1).
#[test]
fn test_sweep_freq_analyzer_resonance_detection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rd_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("rd_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sweep frequency analyzer automatic resonance detection boolean flag",
    );
}
