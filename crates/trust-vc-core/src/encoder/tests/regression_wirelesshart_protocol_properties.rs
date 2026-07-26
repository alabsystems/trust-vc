// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// WirelessHART (IEC 62591) industrial wireless protocol properties.
// Frequency-hopping TDMA on IEEE 802.15.4 (2.4 GHz, channels 11-25).

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.declare_var_typed("chan_valid", i32_ty());
    // WirelessHART uses 15 frequency-hopping channels (IEEE 802.15.4 channels 11-25)
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "cv_def",
        "chan_valid == if channels >= 1 && channels <= 15 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "chan_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WirelessHART: 15 channels in [1, 15] range");
}

#[test]
fn update_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_sec", u32_ty());
    ctx.declare_var_typed("rate_valid", i32_ty());
    // Process variable update rate: 4 seconds (typical), range 1-3600s
    ctx.push_obligation(ProofObligation::assume("rs", "rate_sec == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "rv_def",
        "rate_valid == if rate_sec >= 1 && rate_sec <= 3600 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WirelessHART: update rate 4s in [1, 3600] range");
}

#[test]
fn network_devices() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("devices", u32_ty());
    ctx.declare_var_typed("devices_valid", i32_ty());
    // Max devices per network: 80 (typical deployment), range 1-250
    ctx.push_obligation(ProofObligation::assume("dv", "devices == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "dv_def",
        "devices_valid == if devices >= 1 && devices <= 250 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "devices_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WirelessHART: 80 devices in [1, 250] range");
}

#[test]
fn tx_power() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_offset", u32_ty());
    ctx.declare_var_typed("power_valid", i32_ty());
    // Transmit power: -10 to +10 dBm. Offset +20 so range is 10-30 (u32-safe).
    // Value 30 = 10 dBm (max allowed)
    ctx.push_obligation(ProofObligation::assume("po", "power_offset == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "pv_def",
        "power_valid == if power_offset >= 10 && power_offset <= 30 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "power_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "WirelessHART: TX power 10 dBm (offset 30) in [10, 30] range",
    );
}

#[test]
fn slot_duration() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("slot_ms", u32_ty());
    ctx.declare_var_typed("slot_valid", i32_ty());
    // TDMA time slot: 10 ms (standard), range 10-100 ms
    ctx.push_obligation(ProofObligation::assume("sm", "slot_ms == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "sv_def",
        "slot_valid == if slot_ms >= 10 && slot_ms <= 100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "slot_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WirelessHART: TDMA slot 10 ms in [10, 100] range");
}

#[test]
fn superframe_period() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("period_ms", u32_ty());
    ctx.declare_var_typed("period_valid", i32_ty());
    // Superframe period: 4000 ms (4 seconds), range 100-60000 ms
    ctx.push_obligation(ProofObligation::assume("pm", "period_ms == 4000"));
    ctx.push_obligation(ProofObligation::assume(
        "pv_def",
        "period_valid == if period_ms >= 100 && period_ms <= 60000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "period_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "WirelessHART: superframe 4000 ms in [100, 60000] range",
    );
}

#[test]
fn hop_pattern() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pattern", u32_ty());
    ctx.declare_var_typed("pattern_valid", i32_ty());
    // Hop pattern type: 1=graph routing, 2=source routing, 3=superframe-based
    ctx.push_obligation(ProofObligation::assume("pt", "pattern == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "pv_def",
        "pattern_valid == if pattern == 1 || pattern == 2 || pattern == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pattern_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "WirelessHART: hop pattern 1 (graph routing) is valid",
    );
}

#[test]
fn security_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("level", u32_ty());
    ctx.declare_var_typed("level_valid", i32_ty());
    // Security: 1=none, 2=per-hop MIC, 3=end-to-end encryption, 4=both (MIC+encryption)
    ctx.push_obligation(ProofObligation::assume("lv", "level == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "lv_def",
        "level_valid == if level == 1 || level == 2 || level == 3 || level == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "level_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "WirelessHART: security level 4 (MIC+encryption) is valid",
    );
}

#[test]
fn battery_life() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("life_months", u32_ty());
    ctx.declare_var_typed("life_ok", i32_ty());
    // Target battery life: 60 months (5 years), minimum 12 months
    ctx.push_obligation(ProofObligation::assume("lm", "life_months == 60"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "life_ok == if life_months >= 12 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "life_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "WirelessHART: battery 60 months >= 12 month minimum",
    );
}

#[test]
fn latency_budget() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("latency_ms", u32_ty());
    ctx.declare_var_typed("latency_ok", i32_ty());
    // End-to-end latency budget: 2000 ms, max 30000 ms
    ctx.push_obligation(ProofObligation::assume("lm", "latency_ms == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "latency_ok == if latency_ms <= 30000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "latency_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "WirelessHART: latency 2000 ms <= 30000 ms max");
}
