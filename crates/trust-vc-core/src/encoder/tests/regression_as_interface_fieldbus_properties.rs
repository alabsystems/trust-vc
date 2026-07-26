// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn slave_count() {
    let mut ctx = VerificationContext::new();
    for v in &["slaves", "slave_min", "slave_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // AS-i v2.1: 1 to 62 slaves per master
    ctx.push_obligation(ProofObligation::assume("sc_val", "slaves == 31"));
    ctx.push_obligation(ProofObligation::assume("sc_min", "slave_min == 1"));
    ctx.push_obligation(ProofObligation::assume("sc_max", "slave_max == 62"));
    ctx.push_obligation(ProofObligation::assert(
        "sc_in_range",
        "slaves >= slave_min && slaves <= slave_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "slave count 31 in range [1,62] (AS-i v2.1 max 62)");
}

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_ms", "cycle_min", "cycle_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Cycle time in ms: typical 5ms for 31 slaves, valid range 1 to 10
    ctx.push_obligation(ProofObligation::assume("ct_val", "cycle_ms == 5"));
    ctx.push_obligation(ProofObligation::assume("ct_min", "cycle_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ct_max", "cycle_max == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "ct_in_range",
        "cycle_ms >= cycle_min && cycle_ms <= cycle_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cycle time 5 ms in range [1,10] (typical 5ms for 31 slaves)",
    );
}

#[test]
fn cable_length() {
    let mut ctx = VerificationContext::new();
    for v in &["length_m", "length_min", "length_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Cable length in meters: value 200, valid range 1 to 300 (max 300m with repeaters)
    ctx.push_obligation(ProofObligation::assume("cl_val", "length_m == 200"));
    ctx.push_obligation(ProofObligation::assume("cl_min", "length_min == 1"));
    ctx.push_obligation(ProofObligation::assume("cl_max", "length_max == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "cl_in_range",
        "length_m >= length_min && length_m <= length_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cable length 200 m in range [1,300] (max 300m with repeaters)",
    );
}

#[test]
fn data_bits() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("data_bits", u32_ty());
    ctx.declare_var_typed("valid_bits", i32_ty());
    // 1=4-bit standard, 2=8-bit A/B, 3=16-bit extended
    ctx.push_obligation(ProofObligation::assume("db_val", "data_bits == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "db_valid_def",
        "valid_bits == if data_bits == 1 || data_bits == 2 || data_bits == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("db_check", "valid_bits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "data bits 2 (8-bit A/B) is valid");
}

#[test]
fn profile_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("profile", u32_ty());
    ctx.declare_var_typed("valid_profile", i32_ty());
    // 1=binary I/O, 2=analog, 3=motion, 4=safety, 5=serial
    ctx.push_obligation(ProofObligation::assume("pr_val", "profile == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "pr_valid_def",
        "valid_profile == if profile == 1 || profile == 2 || profile == 3 || profile == 4 || profile == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("pr_check", "valid_profile == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "profile type 4 (safety) is valid");
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "volt_min", "volt_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Supply voltage in mV DC: nominal 29.5V (29500 mV), valid range 26500 to 31600
    ctx.push_obligation(ProofObligation::assume("sv_val", "voltage_mv == 29500"));
    ctx.push_obligation(ProofObligation::assume("sv_min", "volt_min == 26500"));
    ctx.push_obligation(ProofObligation::assume("sv_max", "volt_max == 31600"));
    ctx.push_obligation(ProofObligation::assert(
        "sv_in_range",
        "voltage_mv >= volt_min && voltage_mv <= volt_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "supply voltage 29500 mV (29.5V) in range [26500,31600] (26.5-31.6V)",
    );
}

#[test]
fn power_per_slave() {
    let mut ctx = VerificationContext::new();
    for v in &["power_mw", "power_min", "power_max"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Power per slave in mW: value 2000 (2W), valid range 1 to 8000 (up to 8W)
    ctx.push_obligation(ProofObligation::assume("ps_val", "power_mw == 2000"));
    ctx.push_obligation(ProofObligation::assume("ps_min", "power_min == 1"));
    ctx.push_obligation(ProofObligation::assume("ps_max", "power_max == 8000"));
    ctx.push_obligation(ProofObligation::assert(
        "ps_in_range",
        "power_mw >= power_min && power_mw <= power_max",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power per slave 2000 mW (2W) in range [1,8000] (up to 8W)",
    );
}

#[test]
fn safety_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("safety", u32_ty());
    ctx.declare_var_typed("valid_safety", i32_ty());
    // 1=no safety, 2=SIL 2, 3=SIL 3
    ctx.push_obligation(ProofObligation::assume("sl_val", "safety == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "sl_valid_def",
        "valid_safety == if safety == 1 || safety == 2 || safety == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("sl_check", "valid_safety == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "safety level 3 (SIL 3) is valid");
}

#[test]
fn addressing_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("addr_mode", i32_ty());
    ctx.declare_var_typed("valid_addr", i32_ty());
    // 1=auto-address, 2=manual
    ctx.push_obligation(ProofObligation::assume("am_val", "addr_mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "am_valid_def",
        "valid_addr == if addr_mode == 1 || addr_mode == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("am_check", "valid_addr == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "addressing mode 1 (auto-address) is valid");
}

#[test]
fn master_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("master", i32_ty());
    ctx.declare_var_typed("valid_master", i32_ty());
    // 1=M0 single master, 2=M1 redundant master
    ctx.push_obligation(ProofObligation::assume("mt_val", "master == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "mt_valid_def",
        "valid_master == if master == 1 || master == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("mt_check", "valid_master == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "master type 2 (M1 redundant master) is valid");
}
