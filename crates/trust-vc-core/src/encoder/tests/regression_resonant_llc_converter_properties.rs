// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn resonant_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_khz", "rf_min", "rf_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Resonant frequency in kHz: value 150, valid range 50 to 1000
    ctx.push_obligation(ProofObligation::assume("rf_val", "freq_khz == 150"));
    ctx.push_obligation(ProofObligation::assume("rf_lo", "rf_min == 50"));
    ctx.push_obligation(ProofObligation::assume("rf_hi", "rf_max == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "rf_in_range",
        "freq_khz >= rf_min && freq_khz <= rf_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resonant frequency 150 kHz in range [50,1000]");
}

#[test]
fn output_power() {
    let mut ctx = VerificationContext::new();
    for v in &["power_w", "op_min", "op_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Output power in watts: value 3300, valid range 10 to 10000
    ctx.push_obligation(ProofObligation::assume("op_val", "power_w == 3300"));
    ctx.push_obligation(ProofObligation::assume("op_lo", "op_min == 10"));
    ctx.push_obligation(ProofObligation::assume("op_hi", "op_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "op_in_range",
        "power_w >= op_min && power_w <= op_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output power 3300 W in range [10,10000]");
}

#[test]
fn input_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vin_dc", "iv_min", "iv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Input voltage in V DC: value 400, valid range 200 to 800
    ctx.push_obligation(ProofObligation::assume("iv_val", "vin_dc == 400"));
    ctx.push_obligation(ProofObligation::assume("iv_lo", "iv_min == 200"));
    ctx.push_obligation(ProofObligation::assume("iv_hi", "iv_max == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "iv_in_range",
        "vin_dc >= iv_min && vin_dc <= iv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input voltage 400 V DC in range [200,800]");
}

#[test]
fn output_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vout_mv", "ov_min", "ov_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Output voltage in mV: value 12000 (12V), valid range 1000 to 60000
    ctx.push_obligation(ProofObligation::assume("ov_val", "vout_mv == 12000"));
    ctx.push_obligation(ProofObligation::assume("ov_lo", "ov_min == 1000"));
    ctx.push_obligation(ProofObligation::assume("ov_hi", "ov_max == 60000"));
    ctx.push_obligation(ProofObligation::assert(
        "ov_in_range",
        "vout_mv >= ov_min && vout_mv <= ov_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output voltage 12000 mV in range [1000,60000]");
}

#[test]
fn efficiency() {
    let mut ctx = VerificationContext::new();
    for v in &["eff_x10", "ef_min", "ef_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Efficiency x10 %: value 965 (96.5%), valid range 900 to 999
    ctx.push_obligation(ProofObligation::assume("ef_val", "eff_x10 == 965"));
    ctx.push_obligation(ProofObligation::assume("ef_lo", "ef_min == 900"));
    ctx.push_obligation(ProofObligation::assume("ef_hi", "ef_max == 999"));
    ctx.push_obligation(ProofObligation::assert(
        "ef_in_range",
        "eff_x10 >= ef_min && eff_x10 <= ef_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "efficiency 965 (96.5%) in range [900,999]");
}

#[test]
fn switching_device() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sw_dev", u32_ty());
    ctx.declare_var_typed("valid_dev", i32_ty());
    // Switching device types: 1=Si MOSFET, 2=SiC MOSFET, 3=GaN FET
    ctx.push_obligation(ProofObligation::assume("sd_val", "sw_dev == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "sd_def",
        "valid_dev == if sw_dev == 1 || sw_dev == 2 || sw_dev == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sd_chk", "valid_dev == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "switching device 2 (SiC MOSFET) is valid type");
}

#[test]
fn output_count() {
    let mut ctx = VerificationContext::new();
    for v in &["n_out", "oc_min", "oc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Multi-output count: value 2, valid range 1 to 4
    ctx.push_obligation(ProofObligation::assume("oc_val", "n_out == 2"));
    ctx.push_obligation(ProofObligation::assume("oc_lo", "oc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("oc_hi", "oc_max == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "oc_in_range",
        "n_out >= oc_min && n_out <= oc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output count 2 in range [1,4]");
}

#[test]
fn regulation_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reg_meth", u32_ty());
    ctx.declare_var_typed("valid_reg", i32_ty());
    // Regulation methods: 1=frequency modulation, 2=burst mode, 3=phase shift
    ctx.push_obligation(ProofObligation::assume("rm_val", "reg_meth == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "rm_def",
        "valid_reg == if reg_meth == 1 || reg_meth == 2 || reg_meth == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("rm_chk", "valid_reg == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "regulation method 1 (frequency modulation) is valid",
    );
}

#[test]
fn transformer_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["ratio_x10", "tr_min", "tr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Transformer turns ratio x10: value 35 (3.5:1), valid range 5 to 200
    ctx.push_obligation(ProofObligation::assume("tr_val", "ratio_x10 == 35"));
    ctx.push_obligation(ProofObligation::assume("tr_lo", "tr_min == 5"));
    ctx.push_obligation(ProofObligation::assume("tr_hi", "tr_max == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "tr_in_range",
        "ratio_x10 >= tr_min && ratio_x10 <= tr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "transformer ratio 35 (3.5:1) in range [5,200]");
}

#[test]
fn zvs_margin() {
    let mut ctx = VerificationContext::new();
    for v in &["zvs_x10", "zm_min", "zm_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // ZVS margin x10 %: value 150 (15.0%), valid range 50 to 300
    ctx.push_obligation(ProofObligation::assume("zm_val", "zvs_x10 == 150"));
    ctx.push_obligation(ProofObligation::assume("zm_lo", "zm_min == 50"));
    ctx.push_obligation(ProofObligation::assume("zm_hi", "zm_max == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "zm_in_range",
        "zvs_x10 >= zm_min && zvs_x10 <= zm_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ZVS margin 150 (15.0%) in range [50,300]");
}
