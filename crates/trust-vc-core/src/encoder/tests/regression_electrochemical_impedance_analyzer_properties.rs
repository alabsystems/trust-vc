// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn frequency_range_low() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_mhz", "min_freq_mhz", "max_freq_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Minimum frequency in mHz: 1 mHz = 0.001 Hz, range [1, 1000] mHz
    ctx.push_obligation(ProofObligation::assume("fv", "freq_mhz == 1"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_mhz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_mhz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_mhz >= min_freq_mhz && freq_mhz <= max_freq_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS analyzer: 1 mHz in [1, 1000] mHz range");
}

#[test]
fn frequency_range_high() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "min_freq_khz", "max_freq_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // Maximum frequency in kHz: 1000 kHz = 1 MHz, range [100, 10000] kHz
    ctx.push_obligation(ProofObligation::assume("fv", "freq_khz == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_freq_khz == 100"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_freq_khz == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if freq_khz >= min_freq_khz && freq_khz <= max_freq_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EIS analyzer: 1000 kHz (1 MHz) in [100, 10000] kHz range",
    );
}

#[test]
fn impedance_range() {
    let mut ctx = VerificationContext::new();
    for v in &["z_ohm", "max_z_ohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("z_ok", i32_ty());
    // Measurement range in ohms: 1 MOhm value, max 100 MOhm
    ctx.push_obligation(ProofObligation::assume("zv", "z_ohm == 1000000"));
    ctx.push_obligation(ProofObligation::assume("mz", "max_z_ohm == 100000000"));
    ctx.push_obligation(ProofObligation::assume(
        "zo_def",
        "z_ok == if z_ohm <= max_z_ohm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "z_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS analyzer: 1 MOhm impedance <= 100 MOhm max");
}

#[test]
fn ac_amplitude() {
    let mut ctx = VerificationContext::new();
    for v in &["ac_mv", "min_ac_mv", "max_ac_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ac_ok", i32_ty());
    // AC excitation amplitude in mV: 10 mV, range [1, 500] mV
    ctx.push_obligation(ProofObligation::assume("av", "ac_mv == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ac_mv == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ac_mv == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "ac_ok == if ac_mv >= min_ac_mv && ac_mv <= max_ac_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "ac_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS analyzer: 10 mV AC amplitude in [1, 500] mV");
}

#[test]
fn dc_bias() {
    let mut ctx = VerificationContext::new();
    for v in &["bias_offset_mv", "min_bias_mv", "max_bias_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bias_ok", i32_ty());
    // DC bias in mV with +5000 offset for +/-5V range: 5000 = 0V, min 0 (-5V), max 10000 (+5V)
    ctx.push_obligation(ProofObligation::assume("bv", "bias_offset_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_bias_mv == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_bias_mv == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bias_ok == if bias_offset_mv >= min_bias_mv && bias_offset_mv <= max_bias_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "bias_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EIS analyzer: 0V DC bias (offset 5000) in [0, 10000] mV offset range",
    );
}

#[test]
fn points_per_decade() {
    let mut ctx = VerificationContext::new();
    for v in &["ppd", "min_ppd", "max_ppd"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ppd_ok", i32_ty());
    // Measurement density: 10 points per decade, range [1, 100]
    ctx.push_obligation(ProofObligation::assume("pv", "ppd == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ppd == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ppd == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "ppd_ok == if ppd >= min_ppd && ppd <= max_ppd { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "ppd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS analyzer: 10 points/decade in [1, 100]");
}

#[test]
fn measurement_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // 4-way: 1=potentiostatic, 2=galvanostatic, 3=pseudo-potentiostatic, 4=hybrid
    ctx.push_obligation(ProofObligation::assume("mv", "mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 1 || mode == 2 || mode == 3 || mode == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EIS analyzer: potentiostatic mode (1) is valid measurement mode",
    );
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["acc_x100", "max_acc_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Impedance accuracy x100 (%): 10 = 0.10%, max 100 = 1.00%
    ctx.push_obligation(ProofObligation::assume("av", "acc_x100 == 10"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_acc_x100 == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if acc_x100 <= max_acc_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS analyzer: 0.10% accuracy <= 1.00% max");
}

#[test]
fn current_range() {
    let mut ctx = VerificationContext::new();
    for v in &["current_na", "max_current_na"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("current_ok", i32_ty());
    // Minimum measurable current in nA: 1 nA, max 100 nA
    ctx.push_obligation(ProofObligation::assume("cv", "current_na == 1"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_current_na == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "current_ok == if current_na <= max_current_na { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS analyzer: 1 nA current <= 100 nA max");
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "min_channels", "max_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ch_ok", i32_ty());
    // Simultaneous measurement channels: 4, range [1, 16]
    ctx.push_obligation(ProofObligation::assume("cv", "channels == 4"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_channels == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_channels == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "ch_ok == if channels >= min_channels && channels <= max_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "ch_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EIS analyzer: 4 channels in [1, 16]");
}
