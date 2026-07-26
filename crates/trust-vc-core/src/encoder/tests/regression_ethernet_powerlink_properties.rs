// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["cycle_us", "min_cycle_us", "max_cycle_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cycle_ok", i32_ty());
    // POWERLINK isochronous cycle: typically 200μs-10ms
    ctx.push_obligation(ProofObligation::assume("cu", "cycle_us == 1000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_cycle_us == 200"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_cycle_us == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cycle_ok == if cycle_us >= min_cycle_us && cycle_us <= max_cycle_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cycle_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 1ms cycle in [200μs, 10ms] → OK");
}

#[test]
fn polling_response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["pres_us", "max_pres_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("pres_ok", i32_ty());
    // Poll Response (PRes) turnaround time
    ctx.push_obligation(ProofObligation::assume("pu", "pres_us == 25"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pres_us == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "pres_ok == if pres_us <= max_pres_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "pres_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 25μs PRes ≤ 100μs max → OK");
}

#[test]
fn async_slot_size() {
    let mut ctx = VerificationContext::new();
    for v in &["async_us", "max_async_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("async_ok", i32_ty());
    // Asynchronous phase: time for non-real-time traffic
    ctx.push_obligation(ProofObligation::assume("au", "async_us == 200"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_async_us == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "async_ok == if async_us <= max_async_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "async_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 200μs async slot ≤ 500μs max → OK");
}

#[test]
fn node_count() {
    let mut ctx = VerificationContext::new();
    for v in &["nodes", "max_nodes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("nodes_ok", i32_ty());
    // Controlled nodes (CN): up to 239
    ctx.push_obligation(ProofObligation::assume("n", "nodes == 20"));
    ctx.push_obligation(ProofObligation::assume("mn", "max_nodes == 239"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "nodes_ok == if nodes <= max_nodes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "nodes_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 20 nodes ≤ 239 max → OK");
}

#[test]
fn payload_size() {
    let mut ctx = VerificationContext::new();
    for v in &["payload_bytes", "max_payload_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("payload_ok", i32_ty());
    // Ethernet payload up to 1500 bytes
    ctx.push_obligation(ProofObligation::assume("pb", "payload_bytes == 256"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_payload_bytes == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "po_def",
        "payload_ok == if payload_bytes <= max_payload_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "payload_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 256-byte payload ≤ 1500 max → OK");
}

#[test]
fn jitter() {
    let mut ctx = VerificationContext::new();
    for v in &["jitter_ns", "max_jitter_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("jitter_ok", i32_ty());
    // Cycle-to-cycle jitter
    ctx.push_obligation(ProofObligation::assume("jn", "jitter_ns == 500"));
    ctx.push_obligation(ProofObligation::assume("mj", "max_jitter_ns == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "jo_def",
        "jitter_ok == if jitter_ns <= max_jitter_ns { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "jitter_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 500ns jitter ≤ 1000ns max → OK");
}

#[test]
fn soc_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["soc_us", "cycle_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("soc_ok", i32_ty());
    // Start of Cycle must be shorter than cycle time
    ctx.push_obligation(ProofObligation::assume("su", "soc_us == 10"));
    ctx.push_obligation(ProofObligation::assume("cu", "cycle_us == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "soc_ok == if soc_us < cycle_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "soc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 10μs SoC < 1000μs cycle → OK");
}

#[test]
fn pres_frame_size() {
    let mut ctx = VerificationContext::new();
    for v in &["frame_bytes", "min_frame_bytes", "max_frame_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("frame_ok", i32_ty());
    // PRes frame: minimum 36 bytes (header), max 1518 (Ethernet)
    ctx.push_obligation(ProofObligation::assume("fb", "frame_bytes == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_frame_bytes == 36"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_frame_bytes == 1518"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "frame_ok == if frame_bytes >= min_frame_bytes && frame_bytes <= max_frame_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "frame_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 100-byte PRes in [36, 1518] → OK");
}

#[test]
fn multiplexing_slots() {
    let mut ctx = VerificationContext::new();
    for v in &["mux_slots", "max_mux_slots"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mux_ok", i32_ty());
    // Multiplexing: multiple CNs share polling slot
    ctx.push_obligation(ProofObligation::assume("ms", "mux_slots == 4"));
    ctx.push_obligation(ProofObligation::assume("mm", "max_mux_slots == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mux_ok == if mux_slots <= max_mux_slots { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mux_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: 4 mux slots ≤ 16 max → OK");
}

#[test]
fn nmt_state() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("state", u32_ty());
    ctx.declare_var_typed("valid_state", i32_ty());
    // Network Management state: 0=init, 1=pre-op, 2=ready, 3=operational, 4=stopped
    ctx.push_obligation(ProofObligation::assume("s", "state == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_state == if state == 0 || state == 1 || state == 2 || state == 3 || state == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_state == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "POWERLINK: state=3 → valid operational NMT state");
}
