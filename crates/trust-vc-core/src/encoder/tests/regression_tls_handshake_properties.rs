// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn handshake_state_progression() {
    // States: 0=Init, 1=ClientHello, 2=ServerHello, 3=KeyExchange, 4=Finished
    let mut ctx = VerificationContext::new();
    for v in &["state_before", "state_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sb", "state_before == 1")); // ClientHello
    ctx.push_obligation(ProofObligation::assume(
        "sa_def",
        "state_after == state_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_server_hello",
        "state_after == 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "progresses",
        "state_after > state_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TLS: ClientHello(1) → ServerHello(2)");
}

#[test]
fn key_material_length() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "master_secret_len",
        "client_key_len",
        "server_key_len",
        "total_material",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ms", "master_secret_len == 48"));
    ctx.push_obligation(ProofObligation::assume("ck", "client_key_len == 16")); // AES-128
    ctx.push_obligation(ProofObligation::assume("sk", "server_key_len == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "tm_def",
        "total_material == master_secret_len + client_key_len + server_key_len",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "total_material == 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "key material: 48 + 16 + 16 = 80 bytes");
}

#[test]
fn cipher_suite_negotiation() {
    // Client offers 3 suites, server picks strongest supported
    let mut ctx = VerificationContext::new();
    for v in &[
        "client_pref_1",
        "client_pref_2",
        "client_pref_3",
        "server_selected",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cp1", "client_pref_1 == 3")); // strongest
    ctx.push_obligation(ProofObligation::assume("cp2", "client_pref_2 == 2"));
    ctx.push_obligation(ProofObligation::assume("cp3", "client_pref_3 == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ss_def",
        "server_selected == client_pref_1",
    )); // pick strongest
    ctx.push_obligation(ProofObligation::assert("is_3", "server_selected == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cipher negotiation: server selects strongest (3)");
}

#[test]
fn session_id_uniqueness() {
    let mut ctx = VerificationContext::new();
    for v in &["session_a", "session_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sa", "session_a == 12345"));
    ctx.push_obligation(ProofObligation::assume("sb", "session_b == 67890"));
    ctx.push_obligation(ProofObligation::assert("unique", "session_a != session_b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "session IDs: 12345 != 67890");
}

#[test]
fn certificate_chain_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["chain_length", "max_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_chain", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cl", "chain_length == 3")); // leaf → intermediate → root
    ctx.push_obligation(ProofObligation::assume("md", "max_depth == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_chain == if chain_length <= max_depth && chain_length > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "valid_chain == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cert chain: 3 <= max 10, > 0 → valid");
}

#[test]
fn protocol_version_minimum() {
    let mut ctx = VerificationContext::new();
    for v in &["offered_version", "min_version"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acceptable", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ov", "offered_version == 13")); // TLS 1.3
    ctx.push_obligation(ProofObligation::assume("mv", "min_version == 12")); // TLS 1.2
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "acceptable == if offered_version >= min_version { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "acceptable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TLS 1.3 (13) >= min 1.2 (12) → acceptable");
}

#[test]
fn session_resumption_saves_roundtrip() {
    let mut ctx = VerificationContext::new();
    for v in &["full_handshake_rtt", "resumed_rtt", "saved"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fh", "full_handshake_rtt == 2"));
    ctx.push_obligation(ProofObligation::assume("rr", "resumed_rtt == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "saved == full_handshake_rtt - resumed_rtt",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "saved == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "faster",
        "resumed_rtt < full_handshake_rtt",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resumption: 1 RTT < 2 RTT, saves 1");
}

#[test]
fn record_layer_max_size() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "payload_size",
        "header_size",
        "mac_size",
        "total_record",
        "max_record",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "payload_size == 16384")); // 2^14
    ctx.push_obligation(ProofObligation::assume("hs", "header_size == 5"));
    ctx.push_obligation(ProofObligation::assume("ms", "mac_size == 32")); // SHA-256
    ctx.push_obligation(ProofObligation::assume(
        "tr_def",
        "total_record == payload_size + header_size + mac_size",
    ));
    ctx.push_obligation(ProofObligation::assume("mr", "max_record == 16709")); // 2^14 + 2048 + some
    ctx.push_obligation(ProofObligation::assert(
        "within",
        "total_record <= max_record",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "record: 16384+5+32=16421 <= 16709 max");
}

#[test]
fn early_data_size_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["early_data_sent", "max_early_data"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("eds", "early_data_sent == 8192"));
    ctx.push_obligation(ProofObligation::assume("med", "max_early_data == 16384"));
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if early_data_sent <= max_early_data { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "early data: 8192 <= 16384 limit");
}

#[test]
fn key_update_increments_generation() {
    let mut ctx = VerificationContext::new();
    for v in &["gen_before", "gen_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("gb", "gen_before == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ga_def",
        "gen_after == gen_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "increments",
        "gen_after > gen_before",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "gen_after == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "key update: generation 0 → 1");
}
