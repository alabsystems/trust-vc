// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn frame_size() {
    let mut ctx = VerificationContext::new();
    for v in &["frame_bytes", "max_frame_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("frame_ok", i32_ty());
    // AMQP max frame size (negotiated)
    ctx.push_obligation(ProofObligation::assume("fb", "frame_bytes == 131072")); // 128KB
    ctx.push_obligation(ProofObligation::assume("mf", "max_frame_bytes == 1048576")); // 1MB
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "frame_ok == if frame_bytes <= max_frame_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "frame_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMQP: 128KB frame ≤ 1MB max → OK");
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "max_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ch_ok", i32_ty());
    // AMQP channel max (16-bit, 0 reserved)
    ctx.push_obligation(ProofObligation::assume("c", "channels == 100"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_channels == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "ch_ok == if channels >= 1 && channels <= max_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ch_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMQP: 100 channels in [1, 65535] → OK");
}

#[test]
fn heartbeat_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["heartbeat_sec", "max_heartbeat_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hb_ok", i32_ty());
    // Connection heartbeat (0 = disabled)
    ctx.push_obligation(ProofObligation::assume("hs", "heartbeat_sec == 60"));
    ctx.push_obligation(ProofObligation::assume("mh", "max_heartbeat_sec == 3600"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hb_ok == if heartbeat_sec <= max_heartbeat_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hb_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMQP: 60s heartbeat ≤ 3600 max → OK");
}

#[test]
fn exchange_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ex_type", u32_ty());
    ctx.declare_var_typed("valid_ex", i32_ty());
    // Exchange types: 1=direct, 2=fanout, 3=topic, 4=headers
    ctx.push_obligation(ProofObligation::assume("et", "ex_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ve_def",
        "valid_ex == if ex_type == 1 || ex_type == 2 || ex_type == 3 || ex_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_ex == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMQP: topic is valid exchange type");
}

#[test]
fn prefetch_count() {
    let mut ctx = VerificationContext::new();
    for v in &["prefetch", "max_prefetch"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pf_ok", i32_ty());
    // Consumer prefetch (QoS)
    ctx.push_obligation(ProofObligation::assume("p", "prefetch == 100"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_prefetch == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pf_ok == if prefetch >= 1 && prefetch <= max_prefetch { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMQP: prefetch 100 in [1, 65535] → OK");
}

#[test]
fn message_ttl() {
    let mut ctx = VerificationContext::new();
    for v in &["ttl_ms", "max_ttl_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ttl_ok", i32_ty());
    // Message time-to-live in milliseconds
    ctx.push_obligation(ProofObligation::assume("tm", "ttl_ms == 60000")); // 1 min
    ctx.push_obligation(ProofObligation::assume("mt", "max_ttl_ms == 86400000")); // 24h
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "ttl_ok == if ttl_ms <= max_ttl_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ttl_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMQP: 60s TTL ≤ 86400s max → OK");
}

#[test]
fn delivery_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Delivery modes: 1=non-persistent, 2=persistent
    ctx.push_obligation(ProofObligation::assume("m", "mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 1 || mode == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMQP: persistent is valid delivery mode");
}

#[test]
fn queue_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["queue_msgs", "max_queue_msgs"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("q_ok", i32_ty());
    // Queue message limit
    ctx.push_obligation(ProofObligation::assume("qm", "queue_msgs == 10000"));
    ctx.push_obligation(ProofObligation::assume("mq", "max_queue_msgs == 1000000"));
    ctx.push_obligation(ProofObligation::assume(
        "qo_def",
        "q_ok == if queue_msgs <= max_queue_msgs { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "q_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMQP: 10000 messages ≤ 1M max → OK");
}

#[test]
fn routing_key_length() {
    let mut ctx = VerificationContext::new();
    for v in &["key_len", "max_key_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("key_ok", i32_ty());
    // Routing key max 255 characters
    ctx.push_obligation(ProofObligation::assume("kl", "key_len == 64"));
    ctx.push_obligation(ProofObligation::assume("mk", "max_key_len == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "ko_def",
        "key_ok == if key_len >= 1 && key_len <= max_key_len { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "key_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMQP: 64-char routing key in [1, 255] → OK");
}

#[test]
fn consumer_count() {
    let mut ctx = VerificationContext::new();
    for v in &["consumers", "max_consumers"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("con_ok", i32_ty());
    // Consumers per queue
    ctx.push_obligation(ProofObligation::assume("c", "consumers == 10"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_consumers == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "con_ok == if consumers <= max_consumers { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "con_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AMQP: 10 consumers ≤ 1000 max → OK");
}
