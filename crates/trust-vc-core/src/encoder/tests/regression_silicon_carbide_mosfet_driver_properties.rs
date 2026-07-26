// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn gate_voltage_on() {
    let mut ctx = VerificationContext::new();
    for v in &["mv", "mv_min", "mv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gate turn-on voltage in mV: value 20000 (20V), valid range 15000-25000 (15V to 25V typical for SiC)
    ctx.push_obligation(ProofObligation::assume("go_val", "mv == 20000"));
    ctx.push_obligation(ProofObligation::assume("go_min", "mv_min == 15000"));
    ctx.push_obligation(ProofObligation::assume("go_max", "mv_max == 25000"));
    ctx.push_obligation(ProofObligation::assert(
        "go_in_range",
        "mv >= mv_min && mv <= mv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gate turn-on voltage 20000 mV in range [15000,25000]",
    );
}

#[test]
fn gate_voltage_off() {
    let mut ctx = VerificationContext::new();
    for v in &["offset", "offset_min", "offset_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gate turn-off voltage offset in mV: -5V represented as 5000, valid range 2000-10000
    // Mapping: actual -5V -> offset 5000, actual -2V -> offset 8000
    ctx.push_obligation(ProofObligation::assume("gf_val", "offset == 5000"));
    ctx.push_obligation(ProofObligation::assume("gf_min", "offset_min == 2000"));
    ctx.push_obligation(ProofObligation::assume("gf_max", "offset_max == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "gf_in_range",
        "offset >= offset_min && offset <= offset_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gate turn-off voltage offset 5000 mV in range [2000,10000]",
    );
}

#[test]
fn peak_source_current() {
    let mut ctx = VerificationContext::new();
    for v in &["ma", "ma_min", "ma_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Peak source (turn-on) current in mA: value 9000, valid range 1000-30000
    ctx.push_obligation(ProofObligation::assume("ps_val", "ma == 9000"));
    ctx.push_obligation(ProofObligation::assume("ps_min", "ma_min == 1000"));
    ctx.push_obligation(ProofObligation::assume("ps_max", "ma_max == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "ps_in_range",
        "ma >= ma_min && ma <= ma_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "peak source current 9000 mA in range [1000,30000]");
}

#[test]
fn peak_sink_current() {
    let mut ctx = VerificationContext::new();
    for v in &["ma", "ma_min", "ma_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Peak sink (turn-off) current in mA: value 15000, valid range 1000-30000
    ctx.push_obligation(ProofObligation::assume("pk_val", "ma == 15000"));
    ctx.push_obligation(ProofObligation::assume("pk_min", "ma_min == 1000"));
    ctx.push_obligation(ProofObligation::assume("pk_max", "ma_max == 30000"));
    ctx.push_obligation(ProofObligation::assert(
        "pk_in_range",
        "ma >= ma_min && ma <= ma_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "peak sink current 15000 mA in range [1000,30000]");
}

#[test]
fn propagation_delay() {
    let mut ctx = VerificationContext::new();
    for v in &["ns", "ns_min", "ns_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Propagation delay in ns: value 35, valid range 10-500
    ctx.push_obligation(ProofObligation::assume("pd_val", "ns == 35"));
    ctx.push_obligation(ProofObligation::assume("pd_min", "ns_min == 10"));
    ctx.push_obligation(ProofObligation::assume("pd_max", "ns_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "pd_in_range",
        "ns >= ns_min && ns <= ns_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "propagation delay 35 ns in range [10,500]");
}

#[test]
fn isolation_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("iso", u32_ty());
    ctx.declare_var_typed("valid_iso", i32_ty());
    // 1=transformer, 2=capacitive, 3=opto
    ctx.push_obligation(ProofObligation::assume("it_val", "iso == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "it_valid_def",
        "valid_iso == if iso == 1 || iso == 2 || iso == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("it_check", "valid_iso == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "isolation type 2 (capacitive) is valid");
}

#[test]
fn blocking_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bv", u32_ty());
    ctx.declare_var_typed("valid_bv", i32_ty());
    // Non-sequential voltage classes: 650, 1200, 1700, 3300
    ctx.push_obligation(ProofObligation::assume("bv_val", "bv == 1200"));
    ctx.push_obligation(ProofObligation::assume(
        "bv_valid_def",
        "valid_bv == if bv == 650 || bv == 1200 || bv == 1700 || bv == 3300 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("bv_check", "valid_bv == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "blocking voltage 1200 V is valid");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["khz", "khz_min", "khz_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Switching frequency in kHz: value 100, valid range 10-500
    ctx.push_obligation(ProofObligation::assume("sf_val", "khz == 100"));
    ctx.push_obligation(ProofObligation::assume("sf_min", "khz_min == 10"));
    ctx.push_obligation(ProofObligation::assume("sf_max", "khz_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "sf_in_range",
        "khz >= khz_min && khz <= khz_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "switching frequency 100 kHz in range [10,500]");
}

#[test]
fn desaturation_detect() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("desat", i32_ty());
    // Boolean flag: 1=desaturation detection enabled, 0=disabled
    ctx.push_obligation(ProofObligation::assume("dd_val", "desat == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "dd_check",
        "desat == 0 || desat == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "desaturation detect flag 1 is valid boolean");
}

#[test]
fn miller_clamp() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("clamp", i32_ty());
    // Boolean flag: 1=Miller clamp active, 0=inactive
    ctx.push_obligation(ProofObligation::assume("mc_val", "clamp == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mc_check",
        "clamp == 0 || clamp == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "miller clamp flag 1 is valid boolean");
}
