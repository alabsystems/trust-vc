// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn current_transfer_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["ctr_pct", "min_ctr_pct", "max_ctr_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ctr_ok", i32_ty());
    // CTR as percentage (50-600% typical)
    ctx.push_obligation(ProofObligation::assume("cp", "ctr_pct == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ctr_pct == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ctr_pct == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "ctr_ok == if ctr_pct >= min_ctr_pct && ctr_pct <= max_ctr_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ctr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optocoupler: 200% CTR in [50, 600] → OK");
}

#[test]
fn isolation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["iso_vrms", "min_iso_vrms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("iso_ok", i32_ty());
    // Isolation voltage rating
    ctx.push_obligation(ProofObligation::assume("iv", "iso_vrms == 5000"));
    ctx.push_obligation(ProofObligation::assume("mi", "min_iso_vrms == 3750"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "iso_ok == if iso_vrms >= min_iso_vrms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "iso_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optocoupler: 5000Vrms isolation ≥ 3750 min → OK");
}

#[test]
fn forward_current() {
    let mut ctx = VerificationContext::new();
    for v in &["if_ma", "max_if_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("if_ok", i32_ty());
    // LED forward current
    ctx.push_obligation(ProofObligation::assume("im", "if_ma == 10"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_if_ma == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "if_ok == if if_ma <= max_if_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "if_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optocoupler: 10mA IF ≤ 60mA max → OK");
}

#[test]
fn bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_khz", "min_bw_khz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // -3dB bandwidth
    ctx.push_obligation(ProofObligation::assume("bk", "bw_khz == 50"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_bw_khz == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_khz >= min_bw_khz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optocoupler: 50kHz bandwidth ≥ 10kHz min → OK");
}

#[test]
fn rise_time() {
    let mut ctx = VerificationContext::new();
    for v in &["rise_us", "max_rise_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rise_ok", i32_ty());
    // Output rise time in microseconds
    ctx.push_obligation(ProofObligation::assume("ru", "rise_us == 4"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_rise_us == 18"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rise_ok == if rise_us <= max_rise_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rise_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optocoupler: 4μs rise time ≤ 18μs max → OK");
}

#[test]
fn collector_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["vce_mv", "max_vce_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vce_ok", i32_ty());
    // Collector-emitter voltage rating
    ctx.push_obligation(ProofObligation::assume("vm", "vce_mv == 30000")); // 30V
    ctx.push_obligation(ProofObligation::assume("mv", "max_vce_mv == 80000")); // 80V
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vce_ok == if vce_mv <= max_vce_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vce_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optocoupler: 30V VCE ≤ 80V max → OK");
}

#[test]
fn output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("out_type", u32_ty());
    ctx.declare_var_typed("valid_out", i32_ty());
    // Output types: 1=phototransistor, 2=photodarlington, 3=phototriac, 4=photoFET, 5=logic
    ctx.push_obligation(ProofObligation::assume("ot", "out_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_out == if out_type == 1 || out_type == 2 || out_type == 3 || out_type == 4 || out_type == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_out == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optocoupler: phototransistor is valid output type");
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.declare_var_typed("valid_ch", i32_ty());
    // Standard channel counts
    ctx.push_obligation(ProofObligation::assume("c", "channels == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_ch == if channels == 1 || channels == 2 || channels == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ch == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optocoupler: 4-channel is valid configuration");
}

#[test]
fn creepage_distance() {
    let mut ctx = VerificationContext::new();
    for v in &["creepage_mm_x10", "min_creepage_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("crp_ok", i32_ty());
    // Package creepage distance (×10 for 0.1mm)
    ctx.push_obligation(ProofObligation::assume("cx", "creepage_mm_x10 == 80")); // 8.0mm
    ctx.push_obligation(ProofObligation::assume("mc", "min_creepage_x10 == 50")); // 5.0mm
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "crp_ok == if creepage_mm_x10 >= min_creepage_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "crp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optocoupler: 8.0mm creepage ≥ 5.0mm min → OK");
}

#[test]
fn dark_current() {
    let mut ctx = VerificationContext::new();
    for v in &["dark_na", "max_dark_na"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dark_ok", i32_ty());
    // Collector dark current in nanoamps
    ctx.push_obligation(ProofObligation::assume("dn", "dark_na == 10"));
    ctx.push_obligation(ProofObligation::assume("md", "max_dark_na == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dark_ok == if dark_na <= max_dark_na { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dark_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Optocoupler: 10nA dark current ≤ 100nA max → OK");
}
