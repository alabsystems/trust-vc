// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn station_address() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "max_address"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("addr_ok", i32_ty());
    // DNP3 station address (16-bit, 65520 = self-address, 65521-65535 reserved)
    ctx.push_obligation(ProofObligation::assume("a", "address == 100"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_address == 65519"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "addr_ok == if address <= max_address { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNP3: address 100 ≤ 65519 max → OK");
}

#[test]
fn fragment_size() {
    let mut ctx = VerificationContext::new();
    for v in &["frag_bytes", "max_frag_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("frag_ok", i32_ty());
    // Application layer fragment size
    ctx.push_obligation(ProofObligation::assume("fb", "frag_bytes == 2048"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_frag_bytes == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "frag_ok == if frag_bytes >= 249 && frag_bytes <= max_frag_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "frag_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNP3: 2048-byte fragment in [249, 4096] → OK");
}

#[test]
fn event_class() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("class", u32_ty());
    ctx.declare_var_typed("valid_class", i32_ty());
    // Event classes: 0=Class0 (static), 1=Class1, 2=Class2, 3=Class3
    ctx.push_obligation(ProofObligation::assume("c", "class == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_class == if class == 0 || class == 1 || class == 2 || class == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_class == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNP3: Class 1 is valid event class");
}

#[test]
fn unsolicited_retries() {
    let mut ctx = VerificationContext::new();
    for v in &["retries", "max_retries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ret_ok", i32_ty());
    // Unsolicited response retry count
    ctx.push_obligation(ProofObligation::assume("r", "retries == 3"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_retries == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "ret_ok == if retries <= max_retries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ret_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNP3: 3 retries ≤ 10 max → OK");
}

#[test]
fn response_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &["timeout_ms", "min_timeout_ms", "max_timeout_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("to_ok", i32_ty());
    // Application layer response timeout
    ctx.push_obligation(ProofObligation::assume("tm", "timeout_ms == 5000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_timeout_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_timeout_ms == 30000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "to_ok == if timeout_ms >= min_timeout_ms && timeout_ms <= max_timeout_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "to_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNP3: 5s timeout in [1, 30] → OK");
}

#[test]
fn data_link_confirm() {
    let mut ctx = VerificationContext::new();
    for v in &["confirm_timeout_ms", "max_confirm_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("conf_ok", i32_ty());
    // Data link layer confirmation timeout
    ctx.push_obligation(ProofObligation::assume("ct", "confirm_timeout_ms == 1000"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_confirm_ms == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "conf_ok == if confirm_timeout_ms <= max_confirm_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "conf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNP3: 1s DL confirm ≤ 5s max → OK");
}

#[test]
fn object_group() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("group", u32_ty());
    ctx.declare_var_typed("valid_group", i32_ty());
    // Common DNP3 object groups: 1=BI, 2=BIevent, 10=BO, 12=CROB, 30=AI, 40=AO
    ctx.push_obligation(ProofObligation::assume("g", "group == 30")); // Analog Input
    ctx.push_obligation(ProofObligation::assume(
        "vg_def",
        "valid_group == if group == 1 || group == 2 || group == 10 || group == 12 || group == 30 || group == 40 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_group == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNP3: Analog Input (30) is valid object group");
}

#[test]
fn event_buffer_size() {
    let mut ctx = VerificationContext::new();
    for v in &["buffer_size", "max_buffer_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("buf_ok", i32_ty());
    // Event buffer entries per point type
    ctx.push_obligation(ProofObligation::assume("bs", "buffer_size == 100"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_buffer_size == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "buf_ok == if buffer_size >= 1 && buffer_size <= max_buffer_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "buf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNP3: 100 event buffer entries in [1, 10000] → OK");
}

#[test]
fn point_count() {
    let mut ctx = VerificationContext::new();
    for v in &["points", "max_points"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pt_ok", i32_ty());
    // Number of data points (per object group)
    ctx.push_obligation(ProofObligation::assume("p", "points == 500"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_points == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pt_ok == if points >= 1 && points <= max_points { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNP3: 500 points in [1, 65535] → OK");
}

#[test]
fn transport_layer_sequence() {
    let mut ctx = VerificationContext::new();
    for v in &["seq_num", "max_seq_num"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("seq_ok", i32_ty());
    // Transport layer sequence number (6-bit, 0-63)
    ctx.push_obligation(ProofObligation::assume("sn", "seq_num == 42"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_seq_num == 63"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "seq_ok == if seq_num <= max_seq_num { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "seq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNP3: seq 42 ≤ 63 (6-bit max) → OK");
}
