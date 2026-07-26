// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn baud_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud", u32_ty());
    ctx.declare_var_typed("valid_br", i32_ty());
    // M-Bus baud rates per EN 13757: 300, 2400, 9600, 38400
    ctx.push_obligation(ProofObligation::assume("br_val", "baud == 9600"));
    ctx.push_obligation(ProofObligation::assume(
        "br_def",
        "valid_br == if baud == 300 || baud == 2400 || baud == 9600 || baud == 38400 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("br_chk", "valid_br == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "baud rate 9600 is valid M-Bus rate (300/2400/9600/38400)",
    );
}

#[test]
fn slave_count() {
    let mut ctx = VerificationContext::new();
    for v in &["sc_val", "sc_min", "sc_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // M-Bus supports 1 to 250 slaves on a single bus segment
    ctx.push_obligation(ProofObligation::assume("sc_val", "sc_val == 64"));
    ctx.push_obligation(ProofObligation::assume("sc_min", "sc_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sc_max", "sc_max == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "sc_in_range",
        "sc_val >= sc_min && sc_val <= sc_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "slave count 64 in range [1,250]");
}

#[test]
fn bus_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["bv_mv", "bv_min", "bv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Bus voltage in millivolts: 21V to 42V (21000 to 42000 mV)
    ctx.push_obligation(ProofObligation::assume("bv_val", "bv_mv == 36000"));
    ctx.push_obligation(ProofObligation::assume("bv_min", "bv_min == 21000"));
    ctx.push_obligation(ProofObligation::assume("bv_max", "bv_max == 42000"));
    ctx.push_obligation(ProofObligation::assert(
        "bv_in_range",
        "bv_mv >= bv_min && bv_mv <= bv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bus voltage 36000 mV (36V) in range [21000,42000]");
}

#[test]
fn medium_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("medium", u32_ty());
    ctx.declare_var_typed("valid_mt", i32_ty());
    // Medium types: 1=electricity, 2=gas, 3=water, 4=heat, 5=steam
    ctx.push_obligation(ProofObligation::assume("mt_val", "medium == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "mt_def",
        "valid_mt == if medium == 1 || medium == 2 || medium == 3 || medium == 4 || medium == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("mt_chk", "valid_mt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "medium type 3 (water) is valid M-Bus metered medium",
    );
}

#[test]
fn primary_address() {
    let mut ctx = VerificationContext::new();
    for v in &["pa_val", "pa_min", "pa_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Primary address range: 0 to 250 (251-255 reserved)
    ctx.push_obligation(ProofObligation::assume("pa_val", "pa_val == 7"));
    ctx.push_obligation(ProofObligation::assume("pa_min", "pa_min == 0"));
    ctx.push_obligation(ProofObligation::assume("pa_max", "pa_max == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "pa_in_range",
        "pa_val >= pa_min && pa_val <= pa_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "primary address 7 in range [0,250]");
}

#[test]
fn telegram_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("telegram", u32_ty());
    ctx.declare_var_typed("valid_tt", i32_ty());
    // Telegram types: 1=SND_NKE, 2=SND_UD, 3=REQ_UD1, 4=REQ_UD2
    ctx.push_obligation(ProofObligation::assume("tt_val", "telegram == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "tt_def",
        "valid_tt == if telegram == 1 || telegram == 2 || telegram == 3 || telegram == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("tt_chk", "valid_tt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "telegram type 4 (REQ_UD2) is valid M-Bus telegram");
}

#[test]
fn data_record_count() {
    let mut ctx = VerificationContext::new();
    for v in &["dr_val", "dr_min", "dr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Data records per telegram: 1 to 64
    ctx.push_obligation(ProofObligation::assume("dr_val", "dr_val == 12"));
    ctx.push_obligation(ProofObligation::assume("dr_min", "dr_min == 1"));
    ctx.push_obligation(ProofObligation::assume("dr_max", "dr_max == 64"));
    ctx.push_obligation(ProofObligation::assert(
        "dr_in_range",
        "dr_val >= dr_min && dr_val <= dr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "data record count 12 in range [1,64]");
}

#[test]
fn encryption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("enc_mode", u32_ty());
    ctx.declare_var_typed("valid_em", i32_ty());
    // Encryption modes: 1=none, 2=AES-128 CBC, 3=AES-128 CTR
    ctx.push_obligation(ProofObligation::assume("em_val", "enc_mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "em_def",
        "valid_em == if enc_mode == 1 || enc_mode == 2 || enc_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("em_chk", "valid_em == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "encryption mode 2 (AES-128 CBC) is valid M-Bus encryption",
    );
}

#[test]
fn wireless_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl_mode", u32_ty());
    ctx.declare_var_typed("valid_wm", i32_ty());
    // Wireless modes: 1=wired only, 2=wireless M-Bus T, 3=wireless M-Bus S
    ctx.push_obligation(ProofObligation::assume("wm_val", "wl_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "wm_def",
        "valid_wm == if wl_mode == 1 || wl_mode == 2 || wl_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("wm_chk", "valid_wm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wireless mode 1 (wired only) is valid M-Bus transport mode",
    );
}

#[test]
fn battery_life() {
    let mut ctx = VerificationContext::new();
    for v in &["bl_mon", "bl_min", "bl_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Battery life in months: 1 to 240 (up to 20 years)
    ctx.push_obligation(ProofObligation::assume("bl_val", "bl_mon == 120"));
    ctx.push_obligation(ProofObligation::assume("bl_min", "bl_min == 1"));
    ctx.push_obligation(ProofObligation::assume("bl_max", "bl_max == 240"));
    ctx.push_obligation(ProofObligation::assert(
        "bl_in_range",
        "bl_mon >= bl_min && bl_mon <= bl_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "battery life 120 months (10 years) in range [1,240]",
    );
}
