// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn propagation_delay() {
    let mut ctx = VerificationContext::new();
    for v in &["delay_ns", "max_delay_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("delay_ok", i32_ty());
    // Signal propagation delay across isolation barrier
    ctx.push_obligation(ProofObligation::assume("dn", "delay_ns == 10"));
    ctx.push_obligation(ProofObligation::assume("md", "max_delay_ns == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "delay_ok == if delay_ns <= max_delay_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "delay_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Digital iso: 10ns delay ≤ 50ns max → OK");
}

#[test]
fn cmti() {
    let mut ctx = VerificationContext::new();
    for v in &["cmti_kvps", "min_cmti_kvps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cmti_ok", i32_ty());
    // Common-Mode Transient Immunity: kV/μs
    ctx.push_obligation(ProofObligation::assume("ck", "cmti_kvps == 100"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_cmti_kvps == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cmti_ok == if cmti_kvps >= min_cmti_kvps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cmti_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Digital iso: 100kV/μs CMTI ≥ 50 min → OK");
}

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["rate_mbps", "min_rate_mbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // Maximum data rate across barrier
    ctx.push_obligation(ProofObligation::assume("rm", "rate_mbps == 150"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_rate_mbps == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if rate_mbps >= min_rate_mbps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Digital iso: 150Mbps ≥ 25Mbps min → rate OK");
}

#[test]
fn isolation_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["iso_vrms", "min_iso_vrms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("iso_ok", i32_ty());
    // Reinforced isolation voltage rating
    ctx.push_obligation(ProofObligation::assume("iv", "iso_vrms == 5000"));
    ctx.push_obligation(ProofObligation::assume("mi", "min_iso_vrms == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "iso_ok == if iso_vrms >= min_iso_vrms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "iso_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Digital iso: 5000Vrms ≥ 3000 min → isolation OK");
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.declare_var_typed("valid_ch", i32_ty());
    // Standard channel counts: 1, 2, 4, 6
    ctx.push_obligation(ProofObligation::assume("c", "channels == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_ch == if channels == 1 || channels == 2 || channels == 4 || channels == 6 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ch == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Digital iso: 4 channels → valid count");
}

#[test]
fn supply_current() {
    let mut ctx = VerificationContext::new();
    for v in &["icc_ma", "max_icc_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("icc_ok", i32_ty());
    // Per-channel supply current
    ctx.push_obligation(ProofObligation::assume("im", "icc_ma == 3"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_icc_ma == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "icc_ok == if icc_ma <= max_icc_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "icc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Digital iso: 3mA Icc ≤ 10mA max → OK");
}

#[test]
fn pulse_width_distortion() {
    let mut ctx = VerificationContext::new();
    for v in &["pwd_ns", "max_pwd_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pwd_ok", i32_ty());
    // Pulse width distortion across barrier
    ctx.push_obligation(ProofObligation::assume("pn", "pwd_ns == 2"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pwd_ns == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pwd_ok == if pwd_ns <= max_pwd_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pwd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Digital iso: 2ns PWD ≤ 5ns max → OK");
}

#[test]
fn output_rise_time() {
    let mut ctx = VerificationContext::new();
    for v in &["rise_ns", "max_rise_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rise_ok", i32_ty());
    // Output signal rise time
    ctx.push_obligation(ProofObligation::assume("rn", "rise_ns == 3"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_rise_ns == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rise_ok == if rise_ns <= max_rise_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rise_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Digital iso: 3ns rise time ≤ 10ns max → OK");
}

#[test]
fn temperature_derating() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_c", "max_temp_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature before voltage derating applies
    ctx.push_obligation(ProofObligation::assume("tc", "temp_c == 85"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_temp_c == 125"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_c <= max_temp_c { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Digital iso: 85°C ≤ 125°C max → no derating");
}

#[test]
fn package_creepage() {
    let mut ctx = VerificationContext::new();
    for v in &["creepage_mm_x10", "min_creepage_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("creep_ok", i32_ty());
    // Package creepage distance (×10 for 0.1mm)
    ctx.push_obligation(ProofObligation::assume("cx", "creepage_mm_x10 == 84")); // 8.4mm
    ctx.push_obligation(ProofObligation::assume("mc", "min_creepage_x10 == 80")); // 8.0mm
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "creep_ok == if creepage_mm_x10 >= min_creepage_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "creep_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Digital iso: 8.4mm creepage ≥ 8.0mm min → OK");
}
