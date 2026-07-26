// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn security_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sl", u32_ty());
    ctx.declare_var_typed("sl_ok", i32_ty());
    // SL1=basic, SL2=intentional, SL3=sophisticated, SL4=state-level
    ctx.push_obligation(ProofObligation::assume("sl_val", "sl == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "sl_def",
        "sl_ok == if sl >= 1 && sl <= 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 62443: SL3 (sophisticated) in [1, 4] range");
}

#[test]
fn zone_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zones", u32_ty());
    ctx.declare_var_typed("zones_ok", i32_ty());
    // Number of security zones in the industrial network
    ctx.push_obligation(ProofObligation::assume("z_val", "zones == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "z_def",
        "zones_ok == if zones >= 1 && zones <= 64 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "zones_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 62443: 8 security zones in [1, 64] range");
}

#[test]
fn conduit_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conduits", u32_ty());
    ctx.declare_var_typed("conduits_ok", i32_ty());
    // Number of conduits between security zones
    ctx.push_obligation(ProofObligation::assume("c_val", "conduits == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "conduits_ok == if conduits >= 1 && conduits <= 128 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "conduits_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 62443: 12 conduits in [1, 128] range");
}

#[test]
fn authentication_factor() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auth", u32_ty());
    ctx.declare_var_typed("valid_auth", i32_ty());
    // 1=password only, 2=two-factor, 3=multi-factor
    ctx.push_obligation(ProofObligation::assume("a_val", "auth == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "valid_auth == if auth == 1 || auth == 2 || auth == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_auth == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 62443: two-factor auth is valid factor type");
}

#[test]
fn session_timeout() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("timeout_sec", u32_ty());
    ctx.declare_var_typed("timeout_ok", i32_ty());
    // Session inactivity timeout in seconds (5 min = 300s)
    ctx.push_obligation(ProofObligation::assume("t_val", "timeout_sec == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "timeout_ok == if timeout_sec >= 60 && timeout_sec <= 3600 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timeout_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "IEC 62443: 300s session timeout in [60, 3600] range",
    );
}

#[test]
fn password_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pwd_len", u32_ty());
    ctx.declare_var_typed("pwd_ok", i32_ty());
    // Minimum password length in characters
    ctx.push_obligation(ProofObligation::assume("p_val", "pwd_len == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "pwd_ok == if pwd_len >= 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pwd_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "IEC 62443: 12-char password meets min 8 requirement",
    );
}

#[test]
fn patch_cycle() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycle_days", u32_ty());
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // Patch management cycle in days, max 90
    ctx.push_obligation(ProofObligation::assume("d_val", "cycle_days == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "cycle_ok == if cycle_days >= 1 && cycle_days <= 90 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 62443: 30-day patch cycle within 90-day max");
}

#[test]
fn audit_log_retention() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("retention_days", u32_ty());
    ctx.declare_var_typed("retention_ok", i32_ty());
    // Audit log retention in days, minimum 90
    ctx.push_obligation(ProofObligation::assume("r_val", "retention_days == 365"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "retention_ok == if retention_days >= 90 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "retention_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 62443: 365-day log retention meets 90-day min");
}

#[test]
fn maturity_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ml", u32_ty());
    ctx.declare_var_typed("ml_ok", i32_ty());
    // ISA/IEC 62443-2-4 maturity: 1=initial, 2=managed, 3=defined, 4=improving
    ctx.push_obligation(ProofObligation::assume("m_val", "ml == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "ml_ok == if ml >= 1 && ml <= 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ml_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "IEC 62443: maturity level 3 (defined) in [1, 4] range",
    );
}

#[test]
fn network_segmentation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seg_type", u32_ty());
    ctx.declare_var_typed("valid_seg", i32_ty());
    // 1=flat, 2=VLAN, 3=firewall, 4=DMZ (demilitarized zone)
    ctx.push_obligation(ProofObligation::assume("s_val", "seg_type == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "valid_seg == if seg_type == 1 || seg_type == 2 || seg_type == 3 || seg_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_seg == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IEC 62443: DMZ segmentation is valid type");
}
