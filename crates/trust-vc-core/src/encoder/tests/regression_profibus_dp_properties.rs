// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn baud_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud_kbps", u32_ty());
    ctx.declare_var_typed("valid_baud", i32_ty());
    // Profibus DP baud rates: 9.6, 19.2, 45.45, 93.75, 187.5, 500, 1500, 3000, 6000, 12000 kbps
    ctx.push_obligation(ProofObligation::assume("bk", "baud_kbps == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "vb_def",
        "valid_baud == if baud_kbps == 9 || baud_kbps == 19 || baud_kbps == 45 || baud_kbps == 93 || baud_kbps == 187 || baud_kbps == 500 || baud_kbps == 1500 || baud_kbps == 3000 || baud_kbps == 6000 || baud_kbps == 12000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_baud == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Profibus: 1500kbps is a valid baud rate");
}

#[test]
fn station_address() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "max_address"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("addr_ok", i32_ty());
    // Profibus addresses: 0-126 (127 = broadcast)
    ctx.push_obligation(ProofObligation::assume("a", "address == 5"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_address == 126"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "addr_ok == if address <= max_address { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Profibus: address 5 ≤ 126 → valid");
}

#[test]
fn data_length() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bytes", "max_data_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("len_ok", i32_ty());
    // Max data per telegram: 244 bytes
    ctx.push_obligation(ProofObligation::assume("db", "data_bytes == 128"));
    ctx.push_obligation(ProofObligation::assume("md", "max_data_bytes == 244"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "len_ok == if data_bytes <= max_data_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "len_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Profibus: 128 bytes ≤ 244 max → data OK");
}

#[test]
fn token_rotation() {
    let mut ctx = VerificationContext::new();
    for v in &["rotation_ms", "max_rotation_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("token_ok", i32_ty());
    // Token rotation time determines determinism
    ctx.push_obligation(ProofObligation::assume("rm", "rotation_ms == 10"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_rotation_ms == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "token_ok == if rotation_ms <= max_rotation_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "token_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Profibus: 10ms token rotation ≤ 50ms max → OK");
}

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_us", "max_cycle_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // DP cycle time: process data exchange period
    ctx.push_obligation(ProofObligation::assume("cu", "cycle_us == 1000"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cycle_us == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cycle_ok == if cycle_us <= max_cycle_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Profibus: 1ms cycle ≤ 5ms max → OK");
}

#[test]
fn diagnostics() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diag_len", u32_ty());
    ctx.declare_var_typed("diag_ok", i32_ty());
    // Standard diagnostics: minimum 6 bytes (station status 1,2,3 + master addr + manufacturer ID)
    ctx.push_obligation(ProofObligation::assume("dl", "diag_len == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "diag_ok == if diag_len >= 6 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "diag_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Profibus: 6-byte diagnostics ≥ 6 min → OK");
}

#[test]
fn gsd_version() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("version", u32_ty());
    ctx.declare_var_typed("is_v2", i32_ty());
    // GSD file version: 1=DP-V0, 2=DP-V1
    ctx.push_obligation(ProofObligation::assume("v", "version == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "is_v2 == if version == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_v2 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Profibus: GSD version=2 → DP-V1");
}

#[test]
fn dp_v1_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // DP modes: 0=DP-V0, 1=DP-V1, 2=DP-V2
    ctx.push_obligation(ProofObligation::assume("m", "mode == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 0 || mode == 1 || mode == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Profibus: mode=1 → valid DP-V1");
}

#[test]
fn watchdog_time() {
    let mut ctx = VerificationContext::new();
    for v in &["watchdog_ms", "min_watchdog_ms", "max_watchdog_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wd_ok", i32_ty());
    // Watchdog: slave goes safe state if no master communication
    ctx.push_obligation(ProofObligation::assume("wm", "watchdog_ms == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_watchdog_ms == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_watchdog_ms == 6500"));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "wd_ok == if watchdog_ms >= min_watchdog_ms && watchdog_ms <= max_watchdog_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "wd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Profibus: 500ms watchdog in [10, 6500] → OK");
}

#[test]
fn slot_time() {
    let mut ctx = VerificationContext::new();
    for v in &["slot_tbit", "min_slot_tbit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("slot_ok", i32_ty());
    // Slot time (Tslot) in bit times: min depends on baud rate
    ctx.push_obligation(ProofObligation::assume("st", "slot_tbit == 300"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_slot_tbit == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "slot_ok == if slot_tbit >= min_slot_tbit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "slot_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Profibus: 300 Tbit slot ≥ 100 min → OK");
}
