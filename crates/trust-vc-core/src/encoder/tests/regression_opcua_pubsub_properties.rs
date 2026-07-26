// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn publishing_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["pub_interval_ms", "min_pub_ms", "max_pub_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pub_ok", i32_ty());
    // OPC UA PubSub publishing interval in milliseconds
    ctx.push_obligation(ProofObligation::assume("pi", "pub_interval_ms == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pub_ms == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pub_ms == 60000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pub_ok == if pub_interval_ms >= min_pub_ms && pub_interval_ms <= max_pub_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pub_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "PubSub: 100ms publishing interval in [1, 60000] -> OK",
    );
}

#[test]
fn writer_group_count() {
    let mut ctx = VerificationContext::new();
    for v in &["wg_count", "min_wg", "max_wg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("wg_ok", i32_ty());
    // Number of writer groups per PubSub connection
    ctx.push_obligation(ProofObligation::assume("wc", "wg_count == 4"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_wg == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_wg == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "wg_ok == if wg_count >= min_wg && wg_count <= max_wg { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "wg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PubSub: 4 writer groups in [1, 64] -> OK");
}

#[test]
fn dataset_fields() {
    let mut ctx = VerificationContext::new();
    for v in &["field_count", "min_fields", "max_fields"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fields_ok", i32_ty());
    // Fields per published dataset
    ctx.push_obligation(ProofObligation::assume("fc", "field_count == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_fields == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_fields == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "fields_ok == if field_count >= min_fields && field_count <= max_fields { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fields_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PubSub: 10 dataset fields in [1, 256] -> OK");
}

#[test]
fn transport_profile() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("profile", u32_ty());
    ctx.declare_var_typed("valid_profile", i32_ty());
    // Transport profiles: 1=UADP/UDP, 2=UADP/Ethernet, 3=JSON/MQTT, 4=JSON/AMQP
    ctx.push_obligation(ProofObligation::assume("p", "profile == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_profile == if profile == 1 || profile == 2 || profile == 3 || profile == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_profile == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PubSub: profile=3 (JSON/MQTT) -> valid transport");
}

#[test]
fn message_security() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sec_mode", u32_ty());
    ctx.declare_var_typed("valid_sec", i32_ty());
    // Message security modes: 1=none, 2=sign, 3=sign+encrypt
    ctx.push_obligation(ProofObligation::assume("sm", "sec_mode == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_sec == if sec_mode == 1 || sec_mode == 2 || sec_mode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_sec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "PubSub: sec_mode=3 (sign+encrypt) -> valid security",
    );
}

#[test]
fn network_message_size() {
    let mut ctx = VerificationContext::new();
    for v in &["msg_size", "min_msg_size", "max_msg_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("size_ok", i32_ty());
    // Max network message size in bytes
    ctx.push_obligation(ProofObligation::assume("ms", "msg_size == 1400"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_msg_size == 64"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_msg_size == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "size_ok == if msg_size >= min_msg_size && msg_size <= max_msg_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "size_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PubSub: 1400-byte message in [64, 65535] -> OK");
}

#[test]
fn keep_alive_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ka_count", "min_ka", "max_ka"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ka_ok", i32_ty());
    // Keep-alive message interval in publishing intervals
    ctx.push_obligation(ProofObligation::assume("kc", "ka_count == 3"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ka == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ka == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ko_def",
        "ka_ok == if ka_count >= min_ka && ka_count <= max_ka { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ka_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PubSub: keep-alive 3 in [1, 100] -> OK");
}

#[test]
fn priority() {
    let mut ctx = VerificationContext::new();
    for v in &["prio", "min_prio", "max_prio"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("prio_ok", i32_ty());
    // Dataset writer priority (0-255)
    ctx.push_obligation(ProofObligation::assume("pr", "prio == 128"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_prio == 0"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_prio == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "prio_ok == if prio >= min_prio && prio <= max_prio { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "prio_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PubSub: priority 128 in [0, 255] -> OK");
}

#[test]
fn key_frame_count() {
    let mut ctx = VerificationContext::new();
    for v in &["kf_count", "min_kf", "max_kf"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("kf_ok", i32_ty());
    // Key frame interval in publishing intervals
    ctx.push_obligation(ProofObligation::assume("kc", "kf_count == 1"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_kf == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_kf == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ko_def",
        "kf_ok == if kf_count >= min_kf && kf_count <= max_kf { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "kf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PubSub: key frame count 1 in [1, 1000] -> OK");
}

#[test]
fn subscriber_count() {
    let mut ctx = VerificationContext::new();
    for v in &["sub_count", "min_sub", "max_sub"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sub_ok", i32_ty());
    // Max subscribers per writer group
    ctx.push_obligation(ProofObligation::assume("sc", "sub_count == 50"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_sub == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_sub == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sub_ok == if sub_count >= min_sub && sub_count <= max_sub { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sub_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PubSub: 50 subscribers in [1, 10000] -> OK");
}
