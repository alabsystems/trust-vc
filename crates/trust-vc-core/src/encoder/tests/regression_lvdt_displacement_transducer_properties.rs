// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn stroke_range() {
    let mut ctx = VerificationContext::new();
    for v in &["range_100mm", "range_min", "range_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Stroke range in hundredths of mm: value 5000 (±25.00mm), offset 2500, bounded 10-50000
    ctx.push_obligation(ProofObligation::assume("sr_val", "range_100mm == 5000"));
    ctx.push_obligation(ProofObligation::assume("sr_min", "range_min == 10"));
    ctx.push_obligation(ProofObligation::assume("sr_max", "range_max == 50000"));
    ctx.push_obligation(ProofObligation::assert(
        "sr_in_range",
        "range_100mm >= range_min && range_100mm <= range_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stroke range 5000 (±25.00mm) in range [10,50000]");
}

#[test]
fn linearity() {
    let mut ctx = VerificationContext::new();
    for v in &["lin_1000pct", "lin_min", "lin_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Linearity in thousandths of % full scale: value 100 (0.100%), bounded 10-5000
    ctx.push_obligation(ProofObligation::assume("ln_val", "lin_1000pct == 100"));
    ctx.push_obligation(ProofObligation::assume("ln_min", "lin_min == 10"));
    ctx.push_obligation(ProofObligation::assume("ln_max", "lin_max == 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "ln_in_range",
        "lin_1000pct >= lin_min && lin_1000pct <= lin_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linearity 100 (0.100% FS) in range [10,5000]");
}

#[test]
fn excitation_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_hz", "freq_min", "freq_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Excitation frequency in Hz: value 3000 (3 kHz), bounded 50-20000
    ctx.push_obligation(ProofObligation::assume("ef_val", "freq_hz == 3000"));
    ctx.push_obligation(ProofObligation::assume("ef_min", "freq_min == 50"));
    ctx.push_obligation(ProofObligation::assume("ef_max", "freq_max == 20000"));
    ctx.push_obligation(ProofObligation::assert(
        "ef_in_range",
        "freq_hz >= freq_min && freq_hz <= freq_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "excitation frequency 3000 Hz (3 kHz) in range [50,20000]",
    );
}

#[test]
fn excitation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "volt_min", "volt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Excitation voltage in mV RMS: value 3000 (3V), bounded 500-10000 (0.5V to 10V)
    ctx.push_obligation(ProofObligation::assume("ev_val", "voltage_mv == 3000"));
    ctx.push_obligation(ProofObligation::assume("ev_min", "volt_min == 500"));
    ctx.push_obligation(ProofObligation::assume("ev_max", "volt_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "ev_in_range",
        "voltage_mv >= volt_min && voltage_mv <= volt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "excitation voltage 3000 mV (3V RMS) in range [500,10000]",
    );
}

#[test]
fn sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["sens_mv_mm", "sens_min", "sens_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Sensitivity in mV/mm at rated excitation: value 40, bounded 1-500
    ctx.push_obligation(ProofObligation::assume("sn_val", "sens_mv_mm == 40"));
    ctx.push_obligation(ProofObligation::assume("sn_min", "sens_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sn_max", "sens_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "sn_in_range",
        "sens_mv_mm >= sens_min && sens_mv_mm <= sens_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensitivity 40 mV/mm in range [1,500]");
}

#[test]
fn core_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("core_mat", u32_ty());
    ctx.declare_var_typed("valid_mat", i32_ty());
    // 1=nickel-iron, 2=permalloy, 3=mu-metal
    ctx.push_obligation(ProofObligation::assume("cm_val", "core_mat == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_valid_def",
        "valid_mat == if core_mat == 1 || core_mat == 2 || core_mat == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cm_check", "valid_mat == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "core material 2 (permalloy) is valid");
}

#[test]
fn output_signal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("out_sig", u32_ty());
    ctx.declare_var_typed("valid_sig", i32_ty());
    // 1=AC ratiometric, 2=DC ±10V, 3=4-20mA, 4=digital
    ctx.push_obligation(ProofObligation::assume("os_val", "out_sig == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "os_valid_def",
        "valid_sig == if out_sig == 1 || out_sig == 2 || out_sig == 3 || out_sig == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("os_check", "valid_sig == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output signal 3 (4-20mA) is valid");
}

#[test]
fn operating_temp() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "temp_min", "temp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating temperature offset +500: value 520 (20°C), bounded 427-773 (-73°C to 273°C)
    ctx.push_obligation(ProofObligation::assume("ot_val", "temp_offset == 520"));
    ctx.push_obligation(ProofObligation::assume("ot_min", "temp_min == 427"));
    ctx.push_obligation(ProofObligation::assume("ot_max", "temp_max == 773"));
    ctx.push_obligation(ProofObligation::assert(
        "ot_in_range",
        "temp_offset >= temp_min && temp_offset <= temp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 520 (20°C offset+500) in range [427,773] (-73°C to 273°C)",
    );
}

#[test]
fn resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["res_nm", "res_min", "res_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Resolution in nm (limited by electronics): value 50, bounded 1-10000
    ctx.push_obligation(ProofObligation::assume("rs_val", "res_nm == 50"));
    ctx.push_obligation(ProofObligation::assume("rs_min", "res_min == 1"));
    ctx.push_obligation(ProofObligation::assume("rs_max", "res_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "rs_in_range",
        "res_nm >= res_min && res_nm <= res_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 50 nm in range [1,10000]");
}

#[test]
fn body_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("body_mat", u32_ty());
    ctx.declare_var_typed("valid_body", i32_ty());
    // 1=stainless steel, 2=titanium, 3=Inconel
    ctx.push_obligation(ProofObligation::assume("bm_val", "body_mat == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "bm_valid_def",
        "valid_body == if body_mat == 1 || body_mat == 2 || body_mat == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("bm_check", "valid_body == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "body material 1 (stainless steel) is valid");
}
