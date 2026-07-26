// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn max_time_allowed() {
    let mut ctx = VerificationContext::new();
    for v in &["time_ms", "max_time_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("time_ok", i32_ty());
    // MaxTime (T0) in milliseconds — max retransmission interval
    ctx.push_obligation(ProofObligation::assume("tm", "time_ms == 4000"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_time_ms == 60000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "time_ok == if time_ms >= 1 && time_ms <= max_time_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "time_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GOOSE: 4s MaxTime in [1, 60000] ms → OK");
}

#[test]
fn min_time() {
    let mut ctx = VerificationContext::new();
    for v in &["min_time_ms", "abs_min_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mt_ok", i32_ty());
    // MinTime — fastest retransmission interval
    ctx.push_obligation(ProofObligation::assume("mm", "min_time_ms == 4")); // 4ms
    ctx.push_obligation(ProofObligation::assume("am", "abs_min_ms == 1")); // 1ms absolute
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mt_ok == if min_time_ms >= abs_min_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GOOSE: 4ms MinTime ≥ 1ms absolute → OK");
}

#[test]
fn dataset_entries() {
    let mut ctx = VerificationContext::new();
    for v in &["entries", "max_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ent_ok", i32_ty());
    // Number of data attributes in GOOSE dataset
    ctx.push_obligation(ProofObligation::assume("e", "entries == 8"));
    ctx.push_obligation(ProofObligation::assume("me", "max_entries == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "ent_ok == if entries >= 1 && entries <= max_entries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ent_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GOOSE: 8 dataset entries in [1, 64] → OK");
}

#[test]
fn state_number() {
    let mut ctx = VerificationContext::new();
    for v in &["st_num", "max_st_num"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("st_ok", i32_ty());
    // StNum increments on each state change (32-bit)
    ctx.push_obligation(ProofObligation::assume("sn", "st_num == 100"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_st_num == 4294967295"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "st_ok == if st_num <= max_st_num { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "st_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GOOSE: StNum 100 ≤ 2^32-1 → OK");
}

#[test]
fn sequence_number() {
    let mut ctx = VerificationContext::new();
    for v in &["sq_num", "max_sq_num"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sq_ok", i32_ty());
    // SqNum increments per retransmission (32-bit)
    ctx.push_obligation(ProofObligation::assume("qn", "sq_num == 50"));
    ctx.push_obligation(ProofObligation::assume("mq", "max_sq_num == 4294967295"));
    ctx.push_obligation(ProofObligation::assume(
        "qo_def",
        "sq_ok == if sq_num <= max_sq_num { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GOOSE: SqNum 50 ≤ 2^32-1 → OK");
}

#[test]
fn config_revision() {
    let mut ctx = VerificationContext::new();
    for v in &["conf_rev", "min_conf_rev"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("conf_ok", i32_ty());
    // ConfRev must be > 0 (0 means unconfigured)
    ctx.push_obligation(ProofObligation::assume("cr", "conf_rev == 1"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_conf_rev == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "conf_ok == if conf_rev >= min_conf_rev { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "conf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GOOSE: ConfRev 1 ≥ 1 min → OK");
}

#[test]
fn vlan_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["priority", "min_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pri_ok", i32_ty());
    // IEEE 802.1Q VLAN priority (3-bit: 0-7, GOOSE typically 4)
    ctx.push_obligation(ProofObligation::assume("p", "priority == 4"));
    ctx.push_obligation(ProofObligation::assume("mp", "min_priority == 4")); // min for GOOSE
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pri_ok == if priority >= min_priority && priority <= 7 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pri_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GOOSE: priority 4 in [4, 7] → OK");
}

#[test]
fn appid() {
    let mut ctx = VerificationContext::new();
    for v in &["appid", "max_appid"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("app_ok", i32_ty());
    // APPID (16-bit, 0x0000-0x3FFF for GOOSE)
    ctx.push_obligation(ProofObligation::assume("ai", "appid == 1000"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_appid == 16383")); // 0x3FFF
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "app_ok == if appid <= max_appid { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "app_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GOOSE: APPID 1000 ≤ 16383 → OK");
}

#[test]
fn transfer_time() {
    let mut ctx = VerificationContext::new();
    for v in &["transfer_ms", "max_transfer_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("xfer_ok", i32_ty());
    // End-to-end transfer time requirement per IEC 61850-5
    ctx.push_obligation(ProofObligation::assume("tm", "transfer_ms == 3")); // Type 1A: 3ms
    ctx.push_obligation(ProofObligation::assume("mt", "max_transfer_ms == 10")); // 10ms max
    ctx.push_obligation(ProofObligation::assume(
        "xo_def",
        "xfer_ok == if transfer_ms <= max_transfer_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "xfer_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GOOSE: 3ms transfer ≤ 10ms max → OK");
}

#[test]
fn needs_commissioning() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nds_com", u32_ty());
    ctx.declare_var_typed("valid_nds", i32_ty());
    // NdsCom (needs commissioning) boolean: 0=no, 1=yes
    ctx.push_obligation(ProofObligation::assume("nc", "nds_com == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "vn_def",
        "valid_nds == if nds_com == 0 || nds_com == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_nds == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "GOOSE: NdsCom=false is valid");
}
