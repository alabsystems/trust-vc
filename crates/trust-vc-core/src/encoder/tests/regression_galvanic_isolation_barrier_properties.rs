// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn isolation_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", u32_ty());
    ctx.push_obligation(ProofObligation::assume("voltage_val", "voltage == 2500"));
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 500 && voltage <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rated_isolation",
        "voltage >= 500 && voltage <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rated isolation voltage 2500 Vrms in range 500-5000",
    );
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume("channels_val", "channels == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "channels_range",
        "channels >= 1 && channels <= 32",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_channel_count",
        "channels >= 1 && channels <= 32",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "4 isolated channels in valid range 1-32");
}

#[test]
fn signal_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sig", u32_ty());
    ctx.declare_var_typed("valid_sig", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sig_val", "sig == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_sig_def",
        "valid_sig == if sig == 1 || sig == 2 || sig == 3 || sig == 4 || sig == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("signal_valid", "valid_sig == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "signal type 1 (4-20mA analog) is valid 5-way disjunction",
    );
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc", u32_ty());
    ctx.declare_var_typed("acc_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("acc_val", "acc == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "acc_ok_def",
        "acc_ok == if acc <= 50 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_within_spec",
        "acc_ok == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "signal transfer accuracy 0.05% (5/100) within max 0.50%",
    );
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("delay", u32_ty());
    ctx.declare_var_typed("delay_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("delay_val", "delay == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "delay_ok_def",
        "delay_ok == if delay <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "response_within_spec",
        "delay_ok == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "signal propagation delay 100 us within max 5000 us",
    );
}

#[test]
fn protection_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prot", u32_ty());
    ctx.declare_var_typed("valid_prot", i32_ty());
    ctx.push_obligation(ProofObligation::assume("prot_val", "prot == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_prot_def",
        "valid_prot == if prot == 1 || prot == 2 || prot == 3 || prot == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "protection_valid",
        "valid_prot == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protection type 1 (Ex i intrinsic safety) is valid 4-way disjunction",
    );
}

#[test]
fn sil_rating() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sil", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sil_val", "sil == 2"));
    ctx.push_obligation(ProofObligation::assume("sil_range", "sil >= 1 && sil <= 3"));
    ctx.push_obligation(ProofObligation::assert("valid_sil", "sil >= 1 && sil <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SIL 2 rating in valid range 1-3 (no SIL 4 for barriers)",
    );
}

#[test]
fn power_consumption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", u32_ty());
    ctx.declare_var_typed("power_ok", i32_ty());
    ctx.push_obligation(ProofObligation::assume("power_val", "power == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "power_ok_def",
        "power_ok == if power <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_within_spec",
        "power_ok == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "per-channel power 200 mW within max 1000 mW");
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp >= 480 && temp <= 560",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_in_range",
        "temp >= 480 && temp <= 560",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temperature 20C (offset 520) in range -20C to 60C (480-560)",
    );
}

#[test]
fn atex_zone() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zone", u32_ty());
    ctx.declare_var_typed("valid_zone", i32_ty());
    ctx.push_obligation(ProofObligation::assume("zone_val", "zone == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "valid_zone_def",
        "valid_zone == if zone == 0 || zone == 1 || zone == 2 || zone == 20 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("zone_valid", "valid_zone == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ATEX Zone 0 (continuous hazard) is valid 4-way disjunction",
    );
}
