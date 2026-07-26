// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn frequency_range() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "min_freq_hz", "max_freq_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Wire resonant frequency in Hz
    ctx.push_obligation(ProofObligation::assume("fh", "freq_hz == 2500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_hz == 400"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_hz == 6000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_hz >= min_freq_hz && freq_hz <= max_freq_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VW: 2500 Hz frequency in [400, 6000] → OK");
}

#[test]
fn sensor_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vw_type", u32_ty());
    ctx.declare_var_typed("valid_type", i32_ty());
    // VW sensor types: 1=piezometer, 2=strain gauge, 3=load cell, 4=earth pressure cell, 5=settlement gauge
    ctx.push_obligation(ProofObligation::assume("vt", "vw_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_type == if vw_type == 1 || vw_type == 2 || vw_type == 3 || vw_type == 4 || vw_type == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_type == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VW: piezometer is valid sensor type");
}

#[test]
fn excitation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["excite_mv", "min_excite_mv", "max_excite_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("exc_ok", i32_ty());
    // Excitation (pluck) voltage in mV
    ctx.push_obligation(ProofObligation::assume("em", "excite_mv == 5000")); // 5V
    ctx.push_obligation(ProofObligation::assume("mn", "min_excite_mv == 1000")); // 1V
    ctx.push_obligation(ProofObligation::assume("mx", "max_excite_mv == 12000")); // 12V
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "exc_ok == if excite_mv >= min_excite_mv && excite_mv <= max_excite_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "exc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VW: 5V excitation in [1, 12] → OK");
}

#[test]
fn cable_resistance() {
    let mut ctx = VerificationContext::new();
    for v in &["cable_ohm", "max_cable_ohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cable_ok", i32_ty());
    // Cable loop resistance in ohms
    ctx.push_obligation(ProofObligation::assume("co", "cable_ohm == 50"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cable_ohm == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cable_ok == if cable_ohm <= max_cable_ohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cable_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VW: 50Ω cable ≤ 500Ω max → OK");
}

#[test]
fn reading_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution_x10", "min_resolution_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Frequency resolution in Hz (×10 for 0.1 Hz)
    ctx.push_obligation(ProofObligation::assume("rx", "resolution_x10 == 1")); // 0.1 Hz
    ctx.push_obligation(ProofObligation::assume("mr", "min_resolution_x10 == 1")); // 0.1 Hz
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if resolution_x10 >= min_resolution_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VW: 0.1 Hz resolution ≥ 0.1 Hz min → OK");
}

#[test]
fn measurement_range_kpa() {
    let mut ctx = VerificationContext::new();
    for v in &["range_kpa", "max_range_kpa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("range_ok", i32_ty());
    // Piezometer pressure range in kPa
    ctx.push_obligation(ProofObligation::assume("rk", "range_kpa == 1000")); // 1 MPa
    ctx.push_obligation(ProofObligation::assume("mr", "max_range_kpa == 35000")); // 35 MPa
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "range_ok == if range_kpa <= max_range_kpa { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "range_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VW: 1 MPa range ≤ 35 MPa max → OK");
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "max_accuracy_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy as % full scale (×100 for 0.01%)
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x100 == 25")); // 0.25% FS
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x100 == 100")); // 1.00% FS
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x100 <= max_accuracy_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VW: 0.25% FS accuracy ≤ 1.00% max → OK");
}

#[test]
fn temperature_range() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature (offset +500): -20°C to 80°C
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 510")); // 10°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 480")); // -20°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 580")); // 80°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VW: 10°C in [-20, 80] → OK");
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "max_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ch_ok", i32_ty());
    // Number of VW channels per datalogger
    ctx.push_obligation(ProofObligation::assume("c", "channels == 16"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_channels == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "ch_ok == if channels >= 1 && channels <= max_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ch_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VW: 16 channels in [1, 64] → OK");
}

#[test]
fn long_term_stability() {
    let mut ctx = VerificationContext::new();
    for v in &["drift_x100", "max_drift_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("drift_ok", i32_ty());
    // Long-term stability drift as % FS per year (×100 for 0.01%)
    ctx.push_obligation(ProofObligation::assume("dx", "drift_x100 == 10")); // 0.10% FS/year
    ctx.push_obligation(ProofObligation::assume("md", "max_drift_x100 == 50")); // 0.50%
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "drift_ok == if drift_x100 <= max_drift_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "drift_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VW: 0.10% FS/year drift ≤ 0.50% max → OK");
}
