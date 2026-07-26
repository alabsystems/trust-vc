// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn potential_range_mv() {
    let mut ctx = VerificationContext::new();
    for v in &["potential_mv", "min_potential_mv", "max_potential_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("potential_ok", i32_ty());
    // Potential in mV, 5000 mV = +2.5V (symmetric around 0 with offset)
    // Range [0, 10000] where 5000 = 0V, 0 = -2.5V, 10000 = +2.5V
    ctx.push_obligation(ProofObligation::assume("pm", "potential_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_potential_mv == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_potential_mv == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "potential_ok == if potential_mv >= min_potential_mv && potential_mv <= max_potential_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "potential_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECW: 5000 mV potential in [0, 10000] -> OK");
}

#[test]
fn current_range_na() {
    let mut ctx = VerificationContext::new();
    for v in &["current_na", "min_current_na", "max_current_na"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("current_ok", i32_ty());
    // Current in nanoamps, 1000000 nA = 1 mA
    ctx.push_obligation(ProofObligation::assume("cn", "current_na == 1000000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_current_na == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "mx",
        "max_current_na == 1000000000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "current_ok == if current_na >= min_current_na && current_na <= max_current_na { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "current_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECW: 1000000 nA current in [1, 1000000000] -> OK");
}

#[test]
fn impedance_frequency_min_hz() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_min_hz", "lower_hz", "upper_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_min_ok", i32_ty());
    // EIS minimum frequency in Hz, range [1, 1000000]
    ctx.push_obligation(ProofObligation::assume("fm", "freq_min_hz == 100"));
    ctx.push_obligation(ProofObligation::assume("lo", "lower_hz == 1"));
    ctx.push_obligation(ProofObligation::assume("hi", "upper_hz == 1000000"));
    ctx.push_obligation(ProofObligation::assume(
        "fmo_def",
        "freq_min_ok == if freq_min_hz >= lower_hz && freq_min_hz <= upper_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_min_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ECW: 100 Hz impedance freq min in [1, 1000000] -> OK",
    );
}

#[test]
fn impedance_frequency_max_khz() {
    let mut ctx = VerificationContext::new();
    for v in &["freq_max_khz", "lower_khz", "upper_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_max_ok", i32_ty());
    // EIS maximum frequency in kHz, range [1, 10000]
    ctx.push_obligation(ProofObligation::assume("fmx", "freq_max_khz == 1000"));
    ctx.push_obligation(ProofObligation::assume("lo", "lower_khz == 1"));
    ctx.push_obligation(ProofObligation::assume("hi", "upper_khz == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "fmxo_def",
        "freq_max_ok == if freq_max_khz >= lower_khz && freq_max_khz <= upper_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_max_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ECW: 1000 kHz impedance freq max in [1, 10000] -> OK",
    );
}

#[test]
fn technique_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("technique", u32_ty());
    ctx.declare_var_typed("valid_technique", i32_ty());
    // Techniques: 1=CV (cyclic voltammetry), 2=EIS (electrochemical impedance spectroscopy),
    // 3=LSV (linear sweep voltammetry), 4=CA (chronoamperometry)
    ctx.push_obligation(ProofObligation::assume("t", "technique == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_technique == if technique == 1 || technique == 2 || technique == 3 || technique == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_technique == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ECW: EIS (2) is valid technique type (CV/EIS/LSV/CA)",
    );
}

#[test]
fn reference_electrode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ref_electrode", u32_ty());
    ctx.declare_var_typed("valid_ref", i32_ty());
    // Reference electrodes: 1=Ag/AgCl, 2=SCE (saturated calomel), 3=SHE (standard hydrogen)
    ctx.push_obligation(ProofObligation::assume("re", "ref_electrode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_ref == if ref_electrode == 1 || ref_electrode == 2 || ref_electrode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ref == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECW: Ag/AgCl (1) is valid reference electrode");
}

#[test]
fn potential_resolution_x100() {
    let mut ctx = VerificationContext::new();
    for v in &["resolution_x100", "min_res_x100", "max_res_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Potential resolution at x100 scale: 0.01 mV -> 1, 0.10 mV -> 10, 1.00 mV -> 100
    // Range [1, 1000] i.e. 0.01 mV to 10.00 mV
    ctx.push_obligation(ProofObligation::assume("rx", "resolution_x100 == 1")); // 0.01 mV
    ctx.push_obligation(ProofObligation::assume("mn", "min_res_x100 == 1")); // 0.01 mV
    ctx.push_obligation(ProofObligation::assume("mx", "max_res_x100 == 1000")); // 10.00 mV
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if resolution_x100 >= min_res_x100 && resolution_x100 <= max_res_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ECW: 0.01 mV resolution (x100=1) in [1, 1000] -> OK",
    );
}

#[test]
fn adc_bit_depth() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bit_depth", u32_ty());
    ctx.declare_var_typed("valid_depth", i32_ty());
    // ADC bit depths: 16, 20, 24, or 32 (non-sequential)
    ctx.push_obligation(ProofObligation::assume("bd", "bit_depth == 24"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_depth == if bit_depth == 16 || bit_depth == 20 || bit_depth == 24 || bit_depth == 32 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_depth == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECW: 24-bit ADC is valid depth (16/20/24/32)");
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature: offset +500, actual 25 C -> 525
    // Range -300 C (200) to 700 C (1200)
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 525")); // 25 C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 200")); // -300 C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 1200")); // 700 C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ECW: 25 C operating temp in [-300, 700] (offset +500) -> OK",
    );
}

#[test]
fn faraday_cage_enabled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("faraday_cage", i32_ty());
    ctx.declare_var_typed("shielded", i32_ty());
    // Faraday cage: boolean flag as i32 (1=enabled, 0=disabled)
    ctx.push_obligation(ProofObligation::assume("fc", "faraday_cage == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sh_def",
        "shielded == if faraday_cage == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "shielded == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECW: faraday cage enabled -> shielded");
}
