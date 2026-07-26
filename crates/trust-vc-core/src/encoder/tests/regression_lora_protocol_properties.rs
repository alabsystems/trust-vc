// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn spreading_factor() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sf", u32_ty());
    ctx.declare_var_typed("is_valid_sf", i32_ty());
    // LoRa spreading factor: SF7-SF12
    ctx.push_obligation(ProofObligation::assume("s", "sf == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "is_valid_sf == if sf >= 7 && sf <= 12 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_valid_sf == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LoRa: SF10 in [7, 12] → valid spreading factor");
}

#[test]
fn bandwidth_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bw_khz", u32_ty());
    ctx.declare_var_typed("is_standard", i32_ty());
    // Common LoRa bandwidths: 125, 250, 500 kHz
    ctx.push_obligation(ProofObligation::assume("bk", "bw_khz == 125"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_standard == if bw_khz == 125 || bw_khz == 250 || bw_khz == 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_standard == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LoRa: 125 kHz → standard bandwidth");
}

#[test]
fn payload_size_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["payload_bytes", "max_payload"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("size_ok", i32_ty());
    // LoRaWAN: max payload depends on data rate, typically 51-222 bytes
    ctx.push_obligation(ProofObligation::assume("pb", "payload_bytes == 50"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_payload == 51")); // DR0
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "size_ok == if payload_bytes <= max_payload { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "size_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LoRa: 50 bytes ≤ 51 max (DR0) → payload OK");
}

#[test]
fn time_on_air() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("toa_ms", u32_ty());
    ctx.declare_var_typed("max_toa_ms", u32_ty());
    ctx.declare_var_typed("within_limit", i32_ty());
    // Time on air depends on SF, BW, payload. Precomputed.
    ctx.push_obligation(ProofObligation::assume("tm", "toa_ms == 1318")); // SF12/125kHz/51bytes
    ctx.push_obligation(ProofObligation::assume("mt", "max_toa_ms == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if toa_ms <= max_toa_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LoRa: ToA 1318ms ≤ 2000ms limit → within limit");
}

#[test]
fn duty_cycle_compliance() {
    let mut ctx = VerificationContext::new();
    for v in &["tx_time_ms", "period_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("duty_pct_x10", u32_ty());
    ctx.declare_var_typed("compliant", i32_ty());
    // EU868: 1% duty cycle = 10 in ×10 scale. Precompute: 1000/100000 × 1000 = 10
    ctx.push_obligation(ProofObligation::assume("tt", "tx_time_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume("pm", "period_ms == 100000"));
    ctx.push_obligation(ProofObligation::assume("dp", "duty_pct_x10 == 10")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compliant == if duty_pct_x10 <= 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "duty_pct_x10 == 10"));
    ctx.push_obligation(ProofObligation::assert("yes", "compliant == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LoRa: 1% duty cycle = 10‰ ≤ 10‰ limit → compliant");
}

#[test]
fn link_budget() {
    let mut ctx = VerificationContext::new();
    for v in &["tx_power_dbm", "path_loss_db", "rx_sensitivity_dbm"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("link_margin_db", u32_ty());
    ctx.declare_var_typed("link_ok", i32_ty());
    // Link budget = TX_power - path_loss - RX_sensitivity (all as offsets)
    // TX=14dBm(141), path=130dB, RX=-137dBm(0 offset). margin=141-130=11
    ctx.push_obligation(ProofObligation::assume("tp", "tx_power_dbm == 141")); // +14dBm
    ctx.push_obligation(ProofObligation::assume("pl", "path_loss_db == 130"));
    ctx.push_obligation(ProofObligation::assume(
        "lm_def",
        "link_margin_db == tx_power_dbm - path_loss_db",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "link_ok == if link_margin_db >= 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_11", "link_margin_db == 11"));
    ctx.push_obligation(ProofObligation::assert("yes", "link_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LoRa: 141 - 130 = 11dB margin ≥ 5dB min → link OK");
}

#[test]
fn device_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("device_class", u32_ty());
    ctx.declare_var_typed("always_listening", i32_ty());
    // LoRaWAN: Class A (0)=lowest power, B (1)=scheduled, C (2)=always listening
    ctx.push_obligation(ProofObligation::assume("dc", "device_class == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "always_listening == if device_class == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "always_listening == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LoRa: Class C → always listening");
}

#[test]
fn rx_window_timing() {
    let mut ctx = VerificationContext::new();
    for v in &["rx1_delay_ms", "expected_delay_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timing_ok", i32_ty());
    // RX1 window: typically 1 second after TX
    ctx.push_obligation(ProofObligation::assume("rd", "rx1_delay_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume("ed", "expected_delay_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timing_ok == if rx1_delay_ms == expected_delay_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timing_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LoRa: RX1 delay 1000ms = expected → timing OK");
}

#[test]
fn adr_data_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["current_dr", "max_dr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dr_valid", i32_ty());
    // ADR: data rate 0-5 (EU868)
    ctx.push_obligation(ProofObligation::assume("cd", "current_dr == 3"));
    ctx.push_obligation(ProofObligation::assume("md", "max_dr == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "dv_def",
        "dr_valid == if current_dr <= max_dr { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dr_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LoRa: DR3 ≤ DR5 max → valid data rate");
}

#[test]
fn frame_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["tx_counter", "rx_counter"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("counter_ahead", i32_ty());
    // Frame counter: RX must be > last seen to prevent replay
    ctx.push_obligation(ProofObligation::assume("tc", "tx_counter == 100"));
    ctx.push_obligation(ProofObligation::assume("rc", "rx_counter == 95"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "counter_ahead == if tx_counter > rx_counter { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "counter_ahead == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LoRa: TX counter 100 > RX 95 → counter ahead (no replay)",
    );
}
