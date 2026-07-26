// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_crosstalk_analyzer_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_mhz", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("freq", "freq_mhz == 2400"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if freq_mhz >= 1 && freq_mhz <= 50000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crosstalk: freq 2400 MHz in [1, 50000]");
}

#[test]
fn test_crosstalk_analyzer_number_of_ports_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_ports", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("np", "num_ports == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if num_ports >= 2 && num_ports <= 64 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crosstalk: 16 ports in [2, 64]");
}

#[test]
fn test_crosstalk_analyzer_dynamic_range_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_off", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Dynamic range offset by +200 dB to avoid negative values
    ctx.push_obligation(ProofObligation::assume(
        "ro",
        "range_off > 200 && range_off < 400",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if range_off > 200 && range_off < 400 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crosstalk: dynamic range offset in (200, 400) dB");
}

#[test]
fn test_crosstalk_analyzer_isolation_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("iso_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Isolation scaled x10 dB; range 0.1 dB to 200.0 dB
    ctx.push_obligation(ProofObligation::assume("iso", "iso_x10 == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if iso_x10 > 0 && iso_x10 < 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crosstalk: isolation 80.0 dB (800/10) in range");
}

#[test]
fn test_crosstalk_analyzer_directivity_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dir_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    // Directivity scaled x10 dB; range 0.1 dB to 100.0 dB
    ctx.push_obligation(ProofObligation::assume("dir", "dir_x10 == 450"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if dir_x10 > 0 && dir_x10 < 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crosstalk: directivity 45.0 dB (450/10) in range");
}

#[test]
fn test_crosstalk_analyzer_measurement_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_per_sec", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ms", "meas_per_sec == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if meas_per_sec >= 1 && meas_per_sec <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crosstalk: 500 meas/sec in [1, 10000]");
}

#[test]
fn test_crosstalk_analyzer_measurement_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mtype", i32_ty());
    // 1=NEXT, 2=FEXT, 3=ACR
    ctx.push_obligation(ProofObligation::assume("mt", "mtype == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "mtype == 1 || mtype == 2 || mtype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crosstalk: meas type FEXT (2) valid");
}

#[test]
fn test_crosstalk_analyzer_connector_interface_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("iface", i32_ty());
    // 1=SMA, 2=N-type, 3=RJ45
    ctx.push_obligation(ProofObligation::assume("if", "iface == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "iface == 1 || iface == 2 || iface == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crosstalk: connector RJ45 (3) valid");
}

#[test]
fn test_crosstalk_analyzer_calibration_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cal", i32_ty());
    // 1=SOLT, 2=TRL, 3=electronic
    ctx.push_obligation(ProofObligation::assume("cm", "cal == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid",
        "cal == 1 || cal == 2 || cal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crosstalk: calibration SOLT (1) valid");
}

#[test]
fn test_crosstalk_analyzer_auto_deembedding_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_deembed", i32_ty());
    ctx.declare_var_typed("enabled", i32_ty());
    // 1=enabled, 0=disabled
    ctx.push_obligation(ProofObligation::assume("ad", "auto_deembed == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "enabled == if auto_deembed == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("on", "enabled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crosstalk: auto de-embedding enabled");
}
