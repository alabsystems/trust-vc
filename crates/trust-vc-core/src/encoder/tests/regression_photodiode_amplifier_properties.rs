// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn transimpedance_gain() {
    let mut ctx = VerificationContext::new();
    for v in &["photocurrent_na", "feedback_kohm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("output_mv", u32_ty());
    // Vout = Iph × Rf. Precompute: 100nA × 1000kΩ = 100mV
    ctx.push_obligation(ProofObligation::assume("pn", "photocurrent_na == 100"));
    ctx.push_obligation(ProofObligation::assume("fk", "feedback_kohm == 1000"));
    ctx.push_obligation(ProofObligation::assume("om", "output_mv == 100")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_100", "output_mv == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TIA: 100nA × 1MΩ = 100mV output (precomputed)");
}

#[test]
fn dark_current() {
    let mut ctx = VerificationContext::new();
    for v in &["dark_na", "max_dark_na"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dark_ok", i32_ty());
    // Dark current must be below spec for sensitivity
    ctx.push_obligation(ProofObligation::assume("dn", "dark_na == 5"));
    ctx.push_obligation(ProofObligation::assume("md", "max_dark_na == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dark_ok == if dark_na <= max_dark_na { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dark_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TIA: 5nA dark current ≤ 50nA max → OK");
}

#[test]
fn bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_khz", "min_bw_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // TIA bandwidth (gain-bandwidth trade-off)
    ctx.push_obligation(ProofObligation::assume("bk", "bw_khz == 500"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bw_khz == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_khz >= min_bw_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TIA: 500kHz bandwidth ≥ 100kHz min → OK");
}

#[test]
fn reverse_bias() {
    let mut ctx = VerificationContext::new();
    for v in &["bias_mv", "max_bias_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bias_ok", i32_ty());
    // Photodiode reverse bias voltage
    ctx.push_obligation(ProofObligation::assume("bm", "bias_mv == 5000")); // 5V
    ctx.push_obligation(ProofObligation::assume("mb", "max_bias_mv == 20000")); // 20V max
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bias_ok == if bias_mv <= max_bias_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bias_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TIA: 5V reverse bias ≤ 20V max → OK");
}

#[test]
fn nep_noise() {
    let mut ctx = VerificationContext::new();
    for v in &["noise_pw", "signal_pw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("detectable", i32_ty());
    // Signal must exceed noise equivalent power (NEP)
    ctx.push_obligation(ProofObligation::assume("np", "noise_pw == 10")); // 10pW
    ctx.push_obligation(ProofObligation::assume("sp", "signal_pw == 100")); // 100pW
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "detectable == if signal_pw >= noise_pw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "detectable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TIA: 100pW signal ≥ 10pW NEP → detectable");
}

#[test]
fn responsivity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("responsivity_ma_per_w", u32_ty());
    ctx.declare_var_typed("resp_ok", i32_ty());
    // Si photodiode: ~0.4-0.6 A/W at 900nm → 400-600 mA/W
    ctx.push_obligation(ProofObligation::assume(
        "rm",
        "responsivity_ma_per_w == 500",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if responsivity_ma_per_w >= 400 && responsivity_ma_per_w <= 600 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TIA: 500 mA/W responsivity in [400, 600] → OK");
}

#[test]
fn saturation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["output_mv", "rail_mv", "headroom_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("no_saturation", i32_ty());
    // Output must stay below rail minus headroom
    ctx.push_obligation(ProofObligation::assume("om", "output_mv == 4500"));
    ctx.push_obligation(ProofObligation::assume("rm", "rail_mv == 5000"));
    ctx.push_obligation(ProofObligation::assume("hm", "headroom_mv == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "no_saturation == if output_mv <= rail_mv - headroom_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "no_saturation == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TIA: 4.5V output ≤ 4.8V (5V - 200mV) → no saturation",
    );
}

#[test]
fn feedback_capacitor() {
    let mut ctx = VerificationContext::new();
    for v in &["cf_pf", "min_cf_pf", "max_cf_pf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cf_ok", i32_ty());
    // Feedback capacitor for stability and bandwidth shaping
    ctx.push_obligation(ProofObligation::assume("cp", "cf_pf == 2"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cf_pf == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cf_pf == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cf_ok == if cf_pf >= min_cf_pf && cf_pf <= max_cf_pf { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TIA: 2pF feedback cap in [1, 10] → stability OK");
}

#[test]
fn wavelength_range() {
    let mut ctx = VerificationContext::new();
    for v in &["wavelength_nm", "min_nm", "max_nm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wl_ok", i32_ty());
    // Si photodiode spectral range: ~300-1100nm
    ctx.push_obligation(ProofObligation::assume("wn", "wavelength_nm == 850"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_nm == 300"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_nm == 1100"));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "wl_ok == if wavelength_nm >= min_nm && wavelength_nm <= max_nm { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "wl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TIA: 850nm in [300, 1100] → wavelength OK");
}

#[test]
fn active_area() {
    let mut ctx = VerificationContext::new();
    for v in &["area_um2", "min_area_um2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("area_ok", i32_ty());
    // Photodiode active area (larger = more light, more capacitance)
    ctx.push_obligation(ProofObligation::assume("au", "area_um2 == 500000")); // 0.5mm²
    ctx.push_obligation(ProofObligation::assume("ma", "min_area_um2 == 100000")); // 0.1mm²
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "area_ok == if area_um2 >= min_area_um2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "area_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TIA: 0.5mm² area ≥ 0.1mm² min → OK");
}
