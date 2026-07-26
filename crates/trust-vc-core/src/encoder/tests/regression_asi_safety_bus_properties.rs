// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn slave_address() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "max_address"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("addr_ok", i32_ty());
    // AS-i slave address: 1-31
    ctx.push_obligation(ProofObligation::assume("a", "address == 15"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_address == 31"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "addr_ok == if address >= 1 && address <= max_address { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AS-i: address 15 in [1, 31] → OK");
}

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_ms", "max_cycle_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // AS-i cycle time: max 5ms for standard, 10ms for extended
    ctx.push_obligation(ProofObligation::assume("cm", "cycle_ms == 5"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cycle_ms == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cycle_ok == if cycle_ms <= max_cycle_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AS-i: 5ms cycle ≤ 10ms max → OK");
}

#[test]
fn data_bits() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("io_bits", u32_ty());
    ctx.declare_var_typed("valid_bits", i32_ty());
    // AS-i IO data bits per slave: 4 (standard) or 8 (extended)
    ctx.push_obligation(ProofObligation::assume("ib", "io_bits == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_bits == if io_bits == 4 || io_bits == 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_bits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AS-i: 4-bit IO is valid configuration");
}

#[test]
fn cable_length() {
    let mut ctx = VerificationContext::new();
    for v in &["length_m", "max_length_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("len_ok", i32_ty());
    // AS-i cable max 100m (200m with repeater)
    ctx.push_obligation(ProofObligation::assume("lm", "length_m == 80"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_length_m == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "len_ok == if length_m <= max_length_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "len_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AS-i: 80m cable ≤ 100m max → OK");
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "min_voltage_mv", "max_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("volt_ok", i32_ty());
    // AS-i supply voltage: 26.5-31.6V (spec) → millivolts
    ctx.push_obligation(ProofObligation::assume("vm", "voltage_mv == 29800")); // 29.8V
    ctx.push_obligation(ProofObligation::assume("mn", "min_voltage_mv == 26500"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_voltage_mv == 31600"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "volt_ok == if voltage_mv >= min_voltage_mv && voltage_mv <= max_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "volt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AS-i: 29.8V supply in [26.5, 31.6] → OK");
}

#[test]
fn safety_response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["srt_ms", "max_srt_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("srt_ok", i32_ty());
    // Safety response time for ASIsafe (SIL 3)
    ctx.push_obligation(ProofObligation::assume("sm", "srt_ms == 40"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_srt_ms == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "srt_ok == if srt_ms <= max_srt_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "srt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AS-i: 40ms safety response ≤ 100ms max → OK");
}

#[test]
fn slave_profile() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("profile_id", u32_ty());
    ctx.declare_var_typed("valid_profile", i32_ty());
    // AS-i slave profiles: standard IO (1), safety (2), analog (3), combo (4), diagnostics (5)
    ctx.push_obligation(ProofObligation::assume("pi", "profile_id == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_profile == if profile_id == 1 || profile_id == 2 || profile_id == 3 || profile_id == 4 || profile_id == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_profile == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AS-i: safety profile is valid slave profile");
}

#[test]
fn watchdog_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["wd_ms", "min_wd_ms", "max_wd_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wd_ok", i32_ty());
    // Communication watchdog timeout
    ctx.push_obligation(ProofObligation::assume("wm", "wd_ms == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_wd_ms == 20"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_wd_ms == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "wd_ok == if wd_ms >= min_wd_ms && wd_ms <= max_wd_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "wd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AS-i: 50ms watchdog in [20, 200] → OK");
}

#[test]
fn master_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("masters", u32_ty());
    ctx.declare_var_typed("valid_masters", i32_ty());
    // AS-i network: 1 master (standard) or 2 (redundant)
    ctx.push_obligation(ProofObligation::assume("m", "masters == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_masters == if masters == 1 || masters == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_masters == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AS-i: 1 master is valid configuration");
}

#[test]
fn power_consumption() {
    let mut ctx = VerificationContext::new();
    for v in &["power_ma", "max_power_ma"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pwr_ok", i32_ty());
    // Per-slave power consumption from AS-i bus
    ctx.push_obligation(ProofObligation::assume("pm", "power_ma == 50"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_power_ma == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pwr_ok == if power_ma <= max_power_ma { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pwr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AS-i: 50mA slave power ≤ 200mA max → OK");
}
