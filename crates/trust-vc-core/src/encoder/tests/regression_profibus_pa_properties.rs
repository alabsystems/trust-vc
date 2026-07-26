// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_bps", u32_ty());
    // PROFIBUS PA fixed data rate: 31.25 kbps
    ctx.push_obligation(ProofObligation::assume("rb", "rate_bps == 31250"));
    ctx.push_obligation(ProofObligation::assert("fixed_rate", "rate_bps == 31250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFIBUS PA: fixed data rate 31250 bps");
}

#[test]
fn station_address() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("address", u32_ty());
    ctx.declare_var_typed("addr_ok", i32_ty());
    // PA device addresses: 0-125 (126=default, 127=broadcast excluded)
    ctx.push_obligation(ProofObligation::assume("a", "address == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "addr_ok == if address <= 125 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFIBUS PA: address 10 in [0, 125] valid");
}

#[test]
fn segment_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length_m", u32_ty());
    ctx.declare_var_typed("len_ok", i32_ty());
    // Max segment length: 1900 meters
    ctx.push_obligation(ProofObligation::assume("lm", "length_m == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "len_ok == if length_m <= 1900 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "len_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFIBUS PA: 1000m segment <= 1900m max");
}

#[test]
fn devices_per_segment() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("devices", u32_ty());
    ctx.declare_var_typed("dev_ok", i32_ty());
    // 1-32 devices per segment
    ctx.push_obligation(ProofObligation::assume("d", "devices == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dev_ok == if devices >= 1 && devices <= 32 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dev_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFIBUS PA: 20 devices in [1, 32] valid");
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_mv", u32_ty());
    ctx.declare_var_typed("volt_ok", i32_ty());
    // Bus voltage: 9V to 32V (9000mV to 32000mV)
    ctx.push_obligation(ProofObligation::assume("vm", "voltage_mv == 24000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "volt_ok == if voltage_mv >= 9000 && voltage_mv <= 32000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "volt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFIBUS PA: 24000mV (24V) in [9V, 32V] valid");
}

#[test]
fn device_current() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_ma", u32_ty());
    ctx.declare_var_typed("curr_ok", i32_ty());
    // Intrinsically safe: max 20mA per device
    ctx.push_obligation(ProofObligation::assume("cm", "current_ma == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "curr_ok == if current_ma <= 20 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "curr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFIBUS PA: 12mA device current <= 20mA max");
}

#[test]
fn profile_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("profile", u32_ty());
    ctx.declare_var_typed("valid_profile", i32_ty());
    // PA profiles: 1=pressure, 2=temperature, 3=flow, 4=level, 5=analyzer, 6=valve positioner
    ctx.push_obligation(ProofObligation::assume("p", "profile == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_profile == if profile == 1 || profile == 2 || profile == 3 || profile == 4 || profile == 5 || profile == 6 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_profile == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFIBUS PA: profile=3 (flow) is valid");
}

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycle_ms", u32_ty());
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // Bus cycle time: 10ms to 5000ms
    ctx.push_obligation(ProofObligation::assume("cm", "cycle_ms == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cycle_ok == if cycle_ms >= 10 && cycle_ms <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFIBUS PA: 100ms cycle in [10, 5000] valid");
}

#[test]
fn telegram_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ttype", u32_ty());
    ctx.declare_var_typed("valid_ttype", i32_ty());
    // Telegram types: 1=SD1 (no data), 2=SD2 (variable data), 3=SD3 (diagnostic), 4=SD4 (token)
    ctx.push_obligation(ProofObligation::assume("t", "ttype == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_ttype == if ttype == 1 || ttype == 2 || ttype == 3 || ttype == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ttype == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "PROFIBUS PA: telegram type=2 (SD2 variable data) is valid",
    );
}

#[test]
fn function_block_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fb_count", u32_ty());
    ctx.declare_var_typed("fb_ok", i32_ty());
    // Function blocks per device: 1-16
    ctx.push_obligation(ProofObligation::assume("fc", "fb_count == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "fb_ok == if fb_count >= 1 && fb_count <= 16 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fb_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PROFIBUS PA: 4 function blocks in [1, 16] valid");
}
