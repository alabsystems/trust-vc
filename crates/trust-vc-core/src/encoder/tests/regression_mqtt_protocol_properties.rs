// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn qos_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("qos", u32_ty());
    ctx.declare_var_typed("valid_qos", i32_ty());
    // MQTT QoS levels: 0=at most once, 1=at least once, 2=exactly once
    ctx.push_obligation(ProofObligation::assume("q", "qos == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vq_def",
        "valid_qos == if qos == 0 || qos == 1 || qos == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_qos == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MQTT: QoS 1 is valid level");
}

#[test]
fn topic_length() {
    let mut ctx = VerificationContext::new();
    for v in &["topic_len", "max_topic_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("topic_ok", i32_ty());
    // Topic string length (UTF-8, max 65535 bytes)
    ctx.push_obligation(ProofObligation::assume("tl", "topic_len == 128"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_topic_len == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "topic_ok == if topic_len >= 1 && topic_len <= max_topic_len { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "topic_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MQTT: 128-byte topic in [1, 65535] → OK");
}

#[test]
fn keep_alive() {
    let mut ctx = VerificationContext::new();
    for v in &["keep_alive_sec", "max_keep_alive_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ka_ok", i32_ty());
    // Keep-alive interval in seconds (0 = disabled)
    ctx.push_obligation(ProofObligation::assume("ks", "keep_alive_sec == 60"));
    ctx.push_obligation(ProofObligation::assume("mk", "max_keep_alive_sec == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "ko_def",
        "ka_ok == if keep_alive_sec <= max_keep_alive_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ka_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MQTT: 60s keep-alive ≤ 65535 max → OK");
}

#[test]
fn payload_size() {
    let mut ctx = VerificationContext::new();
    for v in &["payload_bytes", "max_payload_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pay_ok", i32_ty());
    // MQTT payload max 256MB, but broker typically limits lower
    ctx.push_obligation(ProofObligation::assume("pb", "payload_bytes == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "mp",
        "max_payload_bytes == 1048576",
    )); // 1MB
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pay_ok == if payload_bytes <= max_payload_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pay_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MQTT: 4096 payload ≤ 1MB max → OK");
}

#[test]
fn client_id_length() {
    let mut ctx = VerificationContext::new();
    for v in &["id_len", "min_id_len", "max_id_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("id_ok", i32_ty());
    // Client identifier length (1-23 characters for MQTT 3.1.1)
    ctx.push_obligation(ProofObligation::assume("il", "id_len == 16"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_id_len == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_id_len == 23"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "id_ok == if id_len >= min_id_len && id_len <= max_id_len { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "id_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MQTT: 16-char client ID in [1, 23] → OK");
}

#[test]
fn session_expiry() {
    let mut ctx = VerificationContext::new();
    for v in &["expiry_sec", "max_expiry_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("exp_ok", i32_ty());
    // MQTT 5.0 session expiry interval
    ctx.push_obligation(ProofObligation::assume("es", "expiry_sec == 3600")); // 1 hour
    ctx.push_obligation(ProofObligation::assume("me", "max_expiry_sec == 86400")); // 24 hours
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "exp_ok == if expiry_sec <= max_expiry_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "exp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MQTT: 3600s session expiry ≤ 86400 max → OK");
}

#[test]
fn protocol_version() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("version", u32_ty());
    ctx.declare_var_typed("valid_ver", i32_ty());
    // MQTT versions: 3=3.1, 4=3.1.1, 5=5.0
    ctx.push_obligation(ProofObligation::assume("v", "version == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vv_def",
        "valid_ver == if version == 3 || version == 4 || version == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ver == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MQTT: v3.1.1 (4) is valid protocol version");
}

#[test]
fn inflight_messages() {
    let mut ctx = VerificationContext::new();
    for v in &["inflight", "max_inflight"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("inf_ok", i32_ty());
    // Maximum in-flight QoS 1/2 messages
    ctx.push_obligation(ProofObligation::assume("i", "inflight == 10"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_inflight == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "inf_ok == if inflight <= max_inflight { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "inf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MQTT: 10 in-flight ≤ 65535 max → OK");
}

#[test]
fn topic_alias() {
    let mut ctx = VerificationContext::new();
    for v in &["alias", "max_alias"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("alias_ok", i32_ty());
    // MQTT 5.0 topic alias (1-65535, 0=not used)
    ctx.push_obligation(ProofObligation::assume("a", "alias == 10"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_alias == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "alias_ok == if alias >= 1 && alias <= max_alias { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "alias_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MQTT: topic alias 10 in [1, 100] → OK");
}

#[test]
fn subscription_count() {
    let mut ctx = VerificationContext::new();
    for v in &["subs", "max_subs"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sub_ok", i32_ty());
    // Maximum subscriptions per client
    ctx.push_obligation(ProofObligation::assume("s", "subs == 50"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_subs == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sub_ok == if subs <= max_subs { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sub_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MQTT: 50 subscriptions ≤ 1000 max → OK");
}
