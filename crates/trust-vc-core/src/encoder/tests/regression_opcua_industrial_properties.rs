// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn session_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["timeout_ms", "min_timeout_ms", "max_timeout_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timeout_ok", i32_ty());
    // OPC UA session timeout
    ctx.push_obligation(ProofObligation::assume("tm", "timeout_ms == 30000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_timeout_ms == 10000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_timeout_ms == 600000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timeout_ok == if timeout_ms >= min_timeout_ms && timeout_ms <= max_timeout_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timeout_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC UA: 30s session timeout in [10s, 600s] → OK");
}

#[test]
fn subscription_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["interval_ms", "min_interval_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("int_ok", i32_ty());
    // Publishing interval for subscriptions
    ctx.push_obligation(ProofObligation::assume("im", "interval_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume("mi", "min_interval_ms == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "int_ok == if interval_ms >= min_interval_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "int_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC UA: 1000ms interval ≥ 100ms min → OK");
}

#[test]
fn monitored_items() {
    let mut ctx = VerificationContext::new();
    for v in &["items", "max_items"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("items_ok", i32_ty());
    // Monitored items per subscription
    ctx.push_obligation(ProofObligation::assume("i", "items == 500"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_items == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "io_def",
        "items_ok == if items <= max_items { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "items_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC UA: 500 monitored items ≤ 10000 max → OK");
}

#[test]
fn security_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("valid_mode", i32_ty());
    // Security modes: 0=none, 1=sign, 2=sign+encrypt
    ctx.push_obligation(ProofObligation::assume("m", "mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "vm_def",
        "valid_mode == if mode == 0 || mode == 1 || mode == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_mode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC UA: mode=2 (sign+encrypt) → valid security");
}

#[test]
fn message_size() {
    let mut ctx = VerificationContext::new();
    for v in &["size_bytes", "max_size_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("size_ok", i32_ty());
    // Max message size (configurable, default often 4MB)
    ctx.push_obligation(ProofObligation::assume("sb", "size_bytes == 65536"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_size_bytes == 4194304")); // 4MB
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "size_ok == if size_bytes <= max_size_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "size_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC UA: 64KB message ≤ 4MB max → OK");
}

#[test]
fn keep_alive_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ka_count", "min_ka", "max_ka"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ka_ok", i32_ty());
    // Keep-alive count (publish intervals before keep-alive)
    ctx.push_obligation(ProofObligation::assume("kc", "ka_count == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_ka == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_ka == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "ko_def",
        "ka_ok == if ka_count >= min_ka && ka_count <= max_ka { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ka_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC UA: keep-alive 10 in [1, 100] → OK");
}

#[test]
fn publishing_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["pub_ms", "min_pub_ms", "max_pub_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pub_ok", i32_ty());
    // Actual publishing interval
    ctx.push_obligation(ProofObligation::assume("pm", "pub_ms == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_pub_ms == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_pub_ms == 60000"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pub_ok == if pub_ms >= min_pub_ms && pub_ms <= max_pub_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pub_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC UA: 500ms publishing in [50, 60000] → OK");
}

#[test]
fn queue_size() {
    let mut ctx = VerificationContext::new();
    for v in &["queue", "max_queue"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("queue_ok", i32_ty());
    // Monitored item notification queue
    ctx.push_obligation(ProofObligation::assume("q", "queue == 5"));
    ctx.push_obligation(ProofObligation::assume("mq", "max_queue == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "qo_def",
        "queue_ok == if queue >= 1 && queue <= max_queue { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "queue_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC UA: queue 5 in [1, 100] → OK");
}

#[test]
fn browse_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["depth", "max_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("depth_ok", i32_ty());
    // Address space browse recursion depth
    ctx.push_obligation(ProofObligation::assume("d", "depth == 10"));
    ctx.push_obligation(ProofObligation::assume("md", "max_depth == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "depth_ok == if depth <= max_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "depth_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC UA: browse depth 10 ≤ 50 max → OK");
}

#[test]
fn endpoint_url_length() {
    let mut ctx = VerificationContext::new();
    for v in &["url_len", "max_url_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("url_ok", i32_ty());
    // Endpoint URL string length
    ctx.push_obligation(ProofObligation::assume("ul", "url_len == 64"));
    ctx.push_obligation(ProofObligation::assume("mu", "max_url_len == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "uo_def",
        "url_ok == if url_len <= max_url_len { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "url_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC UA: 64-char URL ≤ 4096 max → OK");
}
