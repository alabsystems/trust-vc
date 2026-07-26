// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Precision Vector Network Analyzer (VNA) property regression tests

use super::*;

#[test]
fn test_vna_frequency_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_ghz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "freq_ghz >= 1 && freq_ghz <= 110",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "freq_ghz == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "freq_ghz >= 1 && freq_ghz <= 110",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "VNA frequency max 110 GHz bounded with value 50 GHz",
    );
}

#[test]
fn test_vna_ports_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ports", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "ports >= 1 && ports <= 8"));
    ctx.push_obligation(ProofObligation::assume("val", "ports == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "ports >= 1 && ports <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VNA test ports bounded 1-8 with value 4");
}

#[test]
fn test_vna_dynamic_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dynamic_range_db", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "dynamic_range_db >= 80 && dynamic_range_db <= 160",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "dynamic_range_db == 140"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "dynamic_range_db >= 80 && dynamic_range_db <= 160",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "VNA dynamic range bounded 80-160 dB with value 140 dB",
    );
}

#[test]
fn test_vna_trace_noise_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trace_noise_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "trace_noise_x100 >= 1 && trace_noise_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "trace_noise_x100 == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "trace_noise_x100 >= 1 && trace_noise_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "VNA trace noise x100 mdB bounded 1-1000 with value 3 (0.03 mdB)",
    );
}

#[test]
fn test_vna_sweep_points_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sweep_points", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sweep_points >= 1 && sweep_points <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "sweep_points == 32001"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sweep_points >= 1 && sweep_points <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "VNA sweep points bounded 1-100000 with value 32001",
    );
}

#[test]
fn test_vna_if_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("if_bandwidth_hz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "if_bandwidth_hz >= 1 && if_bandwidth_hz <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "if_bandwidth_hz == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "if_bandwidth_hz >= 1 && if_bandwidth_hz <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "VNA IF bandwidth bounded 1-10000000 Hz with value 100 Hz",
    );
}

#[test]
fn test_vna_calibration_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cal_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "cal_type >= 1 && cal_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "cal_type == 1 || cal_type == 2 || cal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "VNA calibration type disjunction 1=SOLT 2=TRL 3=ECal",
    );
}

#[test]
fn test_vna_connector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "conn_type >= 1 && conn_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "conn_type == 1 || conn_type == 2 || conn_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "VNA connector type disjunction 1=N-type 2=SMA 3=waveguide",
    );
}

#[test]
fn test_vna_measurement_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "meas_mode >= 1 && meas_mode <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "meas_mode == 1 || meas_mode == 2 || meas_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "VNA measurement mode disjunction 1=S-parameter 2=time-domain 3=mixer",
    );
}

#[test]
fn test_vna_balanced_measurement_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "balanced",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "VNA balanced measurement flag assumed 1 implies conditional equals 1",
    );
}
