// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn admin_has_all_permissions() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("role", u32_ty());
    ctx.declare_var_typed("can_read", i32_ty());
    ctx.declare_var_typed("can_write", i32_ty());
    ctx.declare_var_typed("can_delete", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "role == 0")); // 0 = admin
    ctx.push_obligation(ProofObligation::assume(
        "cr_def",
        "can_read == if role == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "cw_def",
        "can_write == if role == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "cd_def",
        "can_delete == if role == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "all_perms",
        "can_read == 1 && can_write == 1 && can_delete == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "admin role → all permissions");
}

#[test]
fn viewer_read_only() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("role", u32_ty());
    ctx.declare_var_typed("can_read", i32_ty());
    ctx.declare_var_typed("can_write", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "role == 2")); // 2 = viewer
    ctx.push_obligation(ProofObligation::assume("cr_def", "can_read == 1")); // viewers can read
    ctx.push_obligation(ProofObligation::assume(
        "cw_def",
        "can_write == if role == 0 || role == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("read_yes", "can_read == 1"));
    ctx.push_obligation(ProofObligation::assert("write_no", "can_write == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "viewer: can read, cannot write");
}

#[test]
fn permission_bits_mask() {
    // Permissions as bitmask: read=4, write=2, exec=1
    let mut ctx = VerificationContext::new();
    for v in &["perms", "read_mask", "has_read"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "perms == 6")); // rw- = 110
    ctx.push_obligation(ProofObligation::assume("rm", "read_mask == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "hr_def",
        "has_read == perms & read_mask",
    ));
    ctx.push_obligation(ProofObligation::assert("can_read", "has_read > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "perms 6 (rw-): read bit set");
}

#[test]
fn principle_of_least_privilege() {
    // Grant minimum required permissions
    let mut ctx = VerificationContext::new();
    for v in &["needed_perms", "granted_perms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("np", "needed_perms == 4")); // read only
    ctx.push_obligation(ProofObligation::assume("gp", "granted_perms == 4")); // exact match
    ctx.push_obligation(ProofObligation::assert(
        "minimal",
        "granted_perms == needed_perms",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "least privilege: granted == needed");
}

#[test]
fn role_hierarchy_inherits() {
    // Admin > Editor > Viewer
    let mut ctx = VerificationContext::new();
    for v in &["admin_level", "editor_level", "viewer_level"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("al", "admin_level == 3"));
    ctx.push_obligation(ProofObligation::assume("el", "editor_level == 2"));
    ctx.push_obligation(ProofObligation::assume("vl", "viewer_level == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "hierarchy",
        "admin_level > editor_level && editor_level > viewer_level",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "role hierarchy: admin > editor > viewer");
}

#[test]
fn token_expiry() {
    let mut ctx = VerificationContext::new();
    for v in &["issued_at", "ttl", "current_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("token_valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ia", "issued_at == 1000"));
    ctx.push_obligation(ProofObligation::assume("t", "ttl == 3600"));
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 5000")); // > 4600
    ctx.push_obligation(ProofObligation::assume(
        "tv_def",
        "token_valid == if current_time < issued_at + ttl { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("expired", "token_valid == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "time 5000 >= issued 1000 + TTL 3600 → expired");
}

#[test]
fn rate_limit_per_user() {
    let mut ctx = VerificationContext::new();
    for v in &["requests", "limit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("allowed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "requests == 50"));
    ctx.push_obligation(ProofObligation::assume("l", "limit == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "allowed == if requests < limit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "allowed == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "50 requests < 100 limit → allowed");
}

#[test]
fn audit_log_entry_count() {
    let mut ctx = VerificationContext::new();
    for v in &["log_entries", "new_action", "total_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("le", "log_entries == 999"));
    ctx.push_obligation(ProofObligation::assume("na", "new_action == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "te_def",
        "total_entries == log_entries + new_action",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1000", "total_entries == 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "audit log: 999 + 1 = 1000 entries");
}

#[test]
fn multi_factor_requires_both() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("password_ok", i32_ty());
    ctx.declare_var_typed("totp_ok", i32_ty());
    ctx.declare_var_typed("authenticated", i32_ty());
    ctx.push_obligation(ProofObligation::assume("po", "password_ok == 1"));
    ctx.push_obligation(ProofObligation::assume("to", "totp_ok == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "authenticated == if password_ok == 1 && totp_ok == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("authed", "authenticated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MFA: both password and TOTP → authenticated");
}

#[test]
fn session_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["last_activity", "timeout", "current_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("session_expired", i32_ty());
    ctx.push_obligation(ProofObligation::assume("la", "last_activity == 100"));
    ctx.push_obligation(ProofObligation::assume("to", "timeout == 1800")); // 30 min
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 2000")); // > 1900
    ctx.push_obligation(ProofObligation::assume(
        "se_def",
        "session_expired == if current_time - last_activity > timeout { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("expired", "session_expired == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2000 - 100 = 1900 > 1800 timeout → expired");
}
