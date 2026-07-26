// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn frequency_range_mhz() {
    let mut ctx = VerificationContext::new();
    for v in &["freq", "freq_min", "freq_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Frequency range in MHz: value 1000, valid range 1 to 3000
    ctx.push_obligation(ProofObligation::assume("fr_val", "freq == 1000"));
    ctx.push_obligation(ProofObligation::assume("fr_lo", "freq_min == 1"));
    ctx.push_obligation(ProofObligation::assume("fr_hi", "freq_max == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "fr_in_range",
        "freq >= freq_min && freq <= freq_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency 1000 MHz in range [1,3000]");
}

#[test]
fn voltage_range_code() {
    let mut ctx = VerificationContext::new();
    for v in &["vrange", "vrange_min", "vrange_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Voltage range code: value 5, valid range 1 to 10
    ctx.push_obligation(ProofObligation::assume("vr_val", "vrange == 5"));
    ctx.push_obligation(ProofObligation::assume("vr_lo", "vrange_min == 1"));
    ctx.push_obligation(ProofObligation::assume("vr_hi", "vrange_max == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "vr_in_range",
        "vrange >= vrange_min && vrange <= vrange_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage range code 5 in range [1,10]");
}

#[test]
fn amplitude_accuracy_x1000_pct() {
    let mut ctx = VerificationContext::new();
    for v in &["amp_acc", "amp_acc_min", "amp_acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Amplitude accuracy as x1000 percent (e.g., 0.050% = 50), valid range 1 to 1000
    ctx.push_obligation(ProofObligation::assume("aa_val", "amp_acc == 50"));
    ctx.push_obligation(ProofObligation::assume("aa_lo", "amp_acc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("aa_hi", "amp_acc_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "aa_in_range",
        "amp_acc >= amp_acc_min && amp_acc <= amp_acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "amplitude accuracy 50 (0.050%) in range [1,1000]");
}

#[test]
fn phase_accuracy_x100_deg() {
    let mut ctx = VerificationContext::new();
    for v in &["phase_acc", "phase_acc_min", "phase_acc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Phase accuracy as x100 degrees (e.g., 0.10 deg = 10), valid range 1 to 500
    ctx.push_obligation(ProofObligation::assume("pa_val", "phase_acc == 10"));
    ctx.push_obligation(ProofObligation::assume("pa_lo", "phase_acc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("pa_hi", "phase_acc_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "pa_in_range",
        "phase_acc >= phase_acc_min && phase_acc <= phase_acc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "phase accuracy 10 (0.10 deg) in range [1,500]");
}

#[test]
fn dynamic_range_db() {
    let mut ctx = VerificationContext::new();
    for v in &["dynrange", "dynrange_min", "dynrange_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Dynamic range in dB: value 120, valid range 40 to 160
    ctx.push_obligation(ProofObligation::assume("dr_val", "dynrange == 120"));
    ctx.push_obligation(ProofObligation::assume("dr_lo", "dynrange_min == 40"));
    ctx.push_obligation(ProofObligation::assume("dr_hi", "dynrange_max == 160"));
    ctx.push_obligation(ProofObligation::assert(
        "dr_in_range",
        "dynrange >= dynrange_min && dynrange <= dynrange_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dynamic range 120 dB in range [40,160]");
}

#[test]
fn number_of_channels() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "ch_min", "ch_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Number of channels: value 2, valid range 1 to 4
    ctx.push_obligation(ProofObligation::assume("nc_val", "channels == 2"));
    ctx.push_obligation(ProofObligation::assume("nc_lo", "ch_min == 1"));
    ctx.push_obligation(ProofObligation::assume("nc_hi", "ch_max == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "nc_in_range",
        "channels >= ch_min && channels <= ch_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channel count 2 in range [1,4]");
}

#[test]
fn detection_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_mode", u32_ty());
    ctx.declare_var_typed("valid_det", i32_ty());
    // Detection mode: 1=narrowband, 2=broadband, 3=tracking
    ctx.push_obligation(ProofObligation::assume("dm_val", "det_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "dm_def",
        "valid_det == if det_mode == 1 || det_mode == 2 || det_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dm_chk", "valid_det == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection mode 1 (narrowband) is valid mode");
}

#[test]
fn input_impedance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impedance", u32_ty());
    ctx.declare_var_typed("valid_imp", i32_ty());
    // Input impedance: 1=50-ohm, 2=75-ohm, 3=high-z
    ctx.push_obligation(ProofObligation::assume("ii_val", "impedance == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ii_def",
        "valid_imp == if impedance == 1 || impedance == 2 || impedance == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ii_chk", "valid_imp == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input impedance 1 (50-ohm) is valid impedance");
}

#[test]
fn display_format() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_fmt", u32_ty());
    ctx.declare_var_typed("valid_fmt", i32_ty());
    // Display format: 1=polar, 2=rectangular, 3=logarithmic
    ctx.push_obligation(ProofObligation::assume("df_val", "disp_fmt == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "df_def",
        "valid_fmt == if disp_fmt == 1 || disp_fmt == 2 || disp_fmt == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("df_chk", "valid_fmt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "display format 2 (rectangular) is valid format");
}

#[test]
fn automatic_gain_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("agc_flag", i32_ty());
    ctx.declare_var_typed("agc_active", i32_ty());
    // Automatic gain control: boolean flag encoded as i32 (0=off, 1=on)
    ctx.push_obligation(ProofObligation::assume("ag_val", "agc_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ag_def",
        "agc_active == if agc_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ag_chk", "agc_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AGC flag 1 (enabled) asserts active");
}
