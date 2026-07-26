// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_surge_current_ka() {
    let mut ctx = VerificationContext::new();
    for v in &["surge_ka", "min_ka", "max_ka"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("surge_ok", i32_ty());
    // Surge current capacity in kA
    ctx.push_obligation(ProofObligation::assume("sk", "surge_ka == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ka == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ka == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "surge_ok == if surge_ka >= min_ka && surge_ka <= max_ka { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "surge_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LPS: 100 kA surge current in [10, 200] -> OK");
}

#[test]
fn test_protection_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prot_class", u32_ty());
    ctx.declare_var_typed("valid_class", i32_ty());
    // Protection classes: 1=Type1, 2=Type2, 3=Type3, 4=combined
    ctx.push_obligation(ProofObligation::assume("pc", "prot_class == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_class == if prot_class == 1 || prot_class == 2 || prot_class == 3 || prot_class == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_class == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LPS: combined is valid protection class (4-way)");
}

#[test]
fn test_response_time_ns() {
    let mut ctx = VerificationContext::new();
    for v in &["response_ns", "min_ns", "max_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("response_ok", i32_ty());
    // SPD response time in nanoseconds
    ctx.push_obligation(ProofObligation::assume("rn", "response_ns == 25"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ns == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ns == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "response_ok == if response_ns >= min_ns && response_ns <= max_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "response_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LPS: 25 ns response time in [1, 100] -> OK");
}

#[test]
fn test_nominal_voltage_mv() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "min_mv", "max_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voltage_ok", i32_ty());
    // Nominal system voltage in millivolts (230V = 230000 mV)
    ctx.push_obligation(ProofObligation::assume("vm", "voltage_mv == 230000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_mv == 120000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_mv == 690000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "voltage_ok == if voltage_mv >= min_mv && voltage_mv <= max_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "voltage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LPS: 230V nominal voltage in [120V, 690V] -> OK");
}

#[test]
fn test_spd_count() {
    let mut ctx = VerificationContext::new();
    for v in &["spd_count", "min_spd", "max_spd"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("count_ok", i32_ty());
    // Surge protective device count
    ctx.push_obligation(ProofObligation::assume("sc", "spd_count == 3"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_spd == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_spd == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "count_ok == if spd_count >= min_spd && spd_count <= max_spd { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "count_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LPS: 3 SPDs in [1, 12] -> OK");
}

#[test]
fn test_monitoring_channel_count() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "min_ch", "max_ch"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ch_ok", i32_ty());
    // Lightning counter monitoring channels
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 4"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ch == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ch == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "ch_ok == if channels >= min_ch && channels <= max_ch { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ch_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LPS: 4 monitoring channels in [1, 16] -> OK");
}

#[test]
fn test_leakage_current_ua() {
    let mut ctx = VerificationContext::new();
    for v in &["leakage_ua", "min_ua", "max_ua"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("leakage_ok", i32_ty());
    // Diagnostic leakage current in microamps
    ctx.push_obligation(ProofObligation::assume("lu", "leakage_ua == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ua == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ua == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "leakage_ok == if leakage_ua >= min_ua && leakage_ua <= max_ua { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "leakage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LPS: 100 uA leakage in [1, 5000] -> OK");
}

#[test]
fn test_communication_interface() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_type", u32_ty());
    ctx.declare_var_typed("valid_comm", i32_ty());
    // Communication interfaces: 1=dry contact, 2=Modbus, 3=Ethernet
    ctx.push_obligation(ProofObligation::assume("ct", "comm_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_comm == if comm_type == 1 || comm_type == 2 || comm_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_comm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LPS: Modbus is valid communication interface (3-way)",
    );
}

#[test]
fn test_strike_counter_max() {
    let mut ctx = VerificationContext::new();
    for v in &["strike_count", "min_count", "max_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("count_ok", i32_ty());
    // Lightning strike event counter maximum
    ctx.push_obligation(ProofObligation::assume("sc", "strike_count == 100000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_count == 1000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_count == 999999"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "count_ok == if strike_count >= min_count && strike_count <= max_count { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "count_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LPS: 100000 strike count in [1000, 999999] -> OK");
}

#[test]
fn test_remote_alarm_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("remote_alarm_enabled", i32_ty());
    ctx.declare_var_typed("alarm_active", i32_ty());
    // Remote alarm output as boolean flag (i32: 1=enabled, 0=disabled)
    ctx.push_obligation(ProofObligation::assume("ra", "remote_alarm_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "alarm_active == if remote_alarm_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "alarm_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LPS: remote alarm enabled -> active (boolean flag)",
    );
}
