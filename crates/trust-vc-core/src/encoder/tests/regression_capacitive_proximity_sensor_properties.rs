// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sensing_range() {
    let mut ctx = VerificationContext::new();
    for v in &["sr_val", "sr_min", "sr_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Sensing range x10 mm (e.g., 25.0mm = 250), bounded 10-500
    ctx.push_obligation(ProofObligation::assume("sr_v", "sr_val == 250"));
    ctx.push_obligation(ProofObligation::assume("sr_lo", "sr_min == 10"));
    ctx.push_obligation(ProofObligation::assume("sr_hi", "sr_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "sr_in_range",
        "sr_val >= sr_min && sr_val <= sr_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sensing range 250 (25.0mm) in range [10,500]");
}

#[test]
fn diameter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dm_val", u32_ty());
    ctx.declare_var_typed("valid_dm", i32_ty());
    // Diameter in mm: 5-way non-sequential (8, 12, 18, 30, 34)
    ctx.push_obligation(ProofObligation::assume("dm_v", "dm_val == 18"));
    ctx.push_obligation(ProofObligation::assume(
        "dm_def",
        "valid_dm == if dm_val == 8 || dm_val == 12 || dm_val == 18 || dm_val == 30 || dm_val == 34 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("dm_chk", "valid_dm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "diameter 18 mm is valid sensor diameter");
}

#[test]
fn output_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ot_val", u32_ty());
    ctx.declare_var_typed("valid_ot", i32_ty());
    // Output type: 1=PNP NO, 2=PNP NC, 3=NPN NO, 4=NPN NC
    ctx.push_obligation(ProofObligation::assume("ot_v", "ot_val == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ot_def",
        "valid_ot == if ot_val == 1 || ot_val == 2 || ot_val == 3 || ot_val == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ot_chk", "valid_ot == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type 1 (PNP NO) is valid sensor output");
}

#[test]
fn switching_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["sf_val", "sf_min", "sf_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Switching frequency in Hz, bounded 1-500
    ctx.push_obligation(ProofObligation::assume("sf_v", "sf_val == 100"));
    ctx.push_obligation(ProofObligation::assume("sf_lo", "sf_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sf_hi", "sf_max == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "sf_in_range",
        "sf_val >= sf_min && sf_val <= sf_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "switching frequency 100 Hz in range [1,500]");
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["sv_val", "sv_min", "sv_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Supply voltage in mV, bounded 10000-36000 (10V to 36V)
    ctx.push_obligation(ProofObligation::assume("sv_v", "sv_val == 24000"));
    ctx.push_obligation(ProofObligation::assume("sv_lo", "sv_min == 10000"));
    ctx.push_obligation(ProofObligation::assume("sv_hi", "sv_max == 36000"));
    ctx.push_obligation(ProofObligation::assert(
        "sv_in_range",
        "sv_val >= sv_min && sv_val <= sv_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "supply voltage 24000 mV (24V) in range [10000,36000]",
    );
}

#[test]
fn hysteresis() {
    let mut ctx = VerificationContext::new();
    for v in &["hy_val", "hy_min", "hy_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Hysteresis x10 % of range (e.g., 5.0% = 50), bounded 10-200
    ctx.push_obligation(ProofObligation::assume("hy_v", "hy_val == 50"));
    ctx.push_obligation(ProofObligation::assume("hy_lo", "hy_min == 10"));
    ctx.push_obligation(ProofObligation::assume("hy_hi", "hy_max == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "hy_in_range",
        "hy_val >= hy_min && hy_val <= hy_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hysteresis 50 (5.0%) in range [10,200]");
}

#[test]
fn operating_temp() {
    let mut ctx = VerificationContext::new();
    for v in &["tp_val", "tp_min", "tp_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Operating temp offset +500, bounded 475-585 (-25C to 85C)
    ctx.push_obligation(ProofObligation::assume("tp_v", "tp_val == 525"));
    ctx.push_obligation(ProofObligation::assume("tp_lo", "tp_min == 475"));
    ctx.push_obligation(ProofObligation::assume("tp_hi", "tp_max == 585"));
    ctx.push_obligation(ProofObligation::assert(
        "tp_in_range",
        "tp_val >= tp_min && tp_val <= tp_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 525 (25C) in range [475,585]");
}

#[test]
fn ip_rating() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ip_val", u32_ty());
    ctx.declare_var_typed("valid_ip", i32_ty());
    // IP rating: 3-way non-sequential (65, 67, 68)
    ctx.push_obligation(ProofObligation::assume("ip_v", "ip_val == 67"));
    ctx.push_obligation(ProofObligation::assume(
        "ip_def",
        "valid_ip == if ip_val == 65 || ip_val == 67 || ip_val == 68 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ip_chk", "valid_ip == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IP rating 67 is valid sensor IP rating");
}

#[test]
fn flush_mount() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fm_val", i32_ty());
    ctx.declare_var_typed("is_flush", i32_ty());
    // Flush mount: boolean flag (1=flush, 0=non-flush)
    ctx.push_obligation(ProofObligation::assume("fm_v", "fm_val == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "fm_def",
        "is_flush == if fm_val == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fm_chk", "is_flush == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flush mount flag 1 (flush) is valid");
}

#[test]
fn adjustment() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("aj_val", u32_ty());
    ctx.declare_var_typed("valid_aj", i32_ty());
    // Adjustment method: 1=potentiometer, 2=teach-in, 3=IO-Link
    ctx.push_obligation(ProofObligation::assume("aj_v", "aj_val == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "aj_def",
        "valid_aj == if aj_val == 1 || aj_val == 2 || aj_val == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("aj_chk", "valid_aj == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "adjustment 2 (teach-in) is valid sensor adjustment",
    );
}
