// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn word_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bits", u32_ty());
    ctx.declare_var_typed("is_32", i32_ty());
    // ARINC 429: fixed 32-bit word
    ctx.push_obligation(ProofObligation::assume("b", "bits == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "iw_def",
        "is_32 == if bits == 32 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_32 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ARINC429: word size = 32 bits");
}

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_kbps", u32_ty());
    ctx.declare_var_typed("valid_rate", i32_ty());
    // ARINC 429: low speed (12.5kbps) or high speed (100kbps)
    ctx.push_obligation(ProofObligation::assume("rk", "rate_kbps == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_rate == if rate_kbps == 12 || rate_kbps == 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_rate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ARINC429: 100kbps is a valid data rate");
}

#[test]
fn sdi_field() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sdi", u32_ty());
    ctx.declare_var_typed("sdi_valid", i32_ty());
    // Source/Destination Identifier: 2-bit field (0-3)
    ctx.push_obligation(ProofObligation::assume("s", "sdi == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "sv_def",
        "sdi_valid == if sdi <= 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sdi_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ARINC429: SDI=2 ≤ 3 → valid 2-bit field");
}

#[test]
fn ssm_field() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ssm", u32_ty());
    ctx.declare_var_typed("ssm_valid", i32_ty());
    // Sign/Status Matrix: 2-bit field (0=failure, 1=no data, 2=test, 3=normal)
    ctx.push_obligation(ProofObligation::assume("s", "ssm == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "sv_def",
        "ssm_valid == if ssm <= 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ssm_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ARINC429: SSM=3 (normal) ≤ 3 → valid");
}

#[test]
fn label_field() {
    let mut ctx = VerificationContext::new();
    for v in &["label", "max_label"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("label_ok", i32_ty());
    // Label: 8-bit field (0-255), identifies parameter type
    ctx.push_obligation(ProofObligation::assume("l", "label == 203"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_label == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "label_ok == if label <= max_label { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "label_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ARINC429: label 203 ≤ 255 → valid 8-bit");
}

#[test]
fn bnr_data_range() {
    let mut ctx = VerificationContext::new();
    for v in &["value", "max_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("data_ok", i32_ty());
    // BNR (Binary Number Representation): 19-bit data field
    ctx.push_obligation(ProofObligation::assume("v", "value == 262143"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_value == 524287")); // 2^19 - 1
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "data_ok == if value <= max_value { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "data_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ARINC429: BNR value ≤ 524287 (19-bit max) → OK");
}

#[test]
fn parity_bit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("parity", u32_ty());
    ctx.declare_var_typed("parity_ok", i32_ty());
    // Odd parity: bit 32 ensures odd number of 1s
    ctx.push_obligation(ProofObligation::assume("p", "parity == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "parity_ok == if parity == 0 || parity == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "parity_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ARINC429: parity=1 → valid parity bit");
}

#[test]
fn bus_loading() {
    let mut ctx = VerificationContext::new();
    for v in &["load_pct", "max_load_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("load_ok", i32_ty());
    // Bus loading: single transmitter per bus, loading < 100%
    ctx.push_obligation(ProofObligation::assume("lp", "load_pct == 60"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_load_pct == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "load_ok == if load_pct <= max_load_pct { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "load_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ARINC429: 60% bus load ≤ 80% max → OK");
}

#[test]
fn receiver_count() {
    let mut ctx = VerificationContext::new();
    for v in &["receivers", "max_receivers"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rx_ok", i32_ty());
    // ARINC 429: up to 20 receivers per bus
    ctx.push_obligation(ProofObligation::assume("r", "receivers == 8"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_receivers == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rx_ok == if receivers <= max_receivers { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rx_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ARINC429: 8 receivers ≤ 20 max → OK");
}

#[test]
fn transmission_gap() {
    let mut ctx = VerificationContext::new();
    for v in &["gap_us", "min_gap_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("gap_ok", i32_ty());
    // Inter-word gap: minimum 4 bit times (40μs at 100kbps)
    ctx.push_obligation(ProofObligation::assume("gu", "gap_us == 64"));
    ctx.push_obligation(ProofObligation::assume("mg", "min_gap_us == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "go_def",
        "gap_ok == if gap_us >= min_gap_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "gap_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ARINC429: 64μs gap ≥ 40μs min → OK");
}
