// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ttl_decreases_over_time() {
    let mut ctx = VerificationContext::new();
    for v in &["original_ttl", "elapsed", "remaining_ttl"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ot", "original_ttl == 3600"));
    ctx.push_obligation(ProofObligation::assume("el", "elapsed == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "rt_def",
        "remaining_ttl == original_ttl - elapsed",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2600", "remaining_ttl == 2600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TTL: 3600 - 1000 = 2600 remaining");
}

#[test]
fn cache_entry_expired() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("remaining_ttl", u32_ty());
    ctx.declare_var_typed("expired", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rt", "remaining_ttl == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "expired == if remaining_ttl == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_expired", "expired == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TTL 0 → cache entry expired");
}

#[test]
fn round_robin_server_selection() {
    let mut ctx = VerificationContext::new();
    for v in &["current", "num_servers", "next_server"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("c", "current == 2"));
    ctx.push_obligation(ProofObligation::assume("ns", "num_servers == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next_server == if current + 1 >= num_servers { 0 } else { current + 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "next_server == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "round robin: server 2 of 3 → wraps to 0");
}

#[test]
fn query_id_uniqueness() {
    let mut ctx = VerificationContext::new();
    for v in &["query_id_1", "query_id_2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("qi1", "query_id_1 == 12345"));
    ctx.push_obligation(ProofObligation::assume("qi2", "query_id_2 == 54321"));
    ctx.push_obligation(ProofObligation::assert(
        "unique",
        "query_id_1 != query_id_2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "query IDs 12345 and 54321 are distinct");
}

#[test]
fn retry_with_next_nameserver() {
    let mut ctx = VerificationContext::new();
    for v in &["current_ns", "total_ns", "next_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cn", "current_ns == 0"));
    ctx.push_obligation(ProofObligation::assume("tn", "total_ns == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "nn_def",
        "next_ns == current_ns + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "next_ns == 1"));
    ctx.push_obligation(ProofObligation::assert("in_range", "next_ns < total_ns"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "retry: nameserver 0 → 1 (of 3)");
}

#[test]
fn response_matches_query() {
    let mut ctx = VerificationContext::new();
    for v in &["query_id", "response_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("matches", i32_ty());
    ctx.push_obligation(ProofObligation::assume("qi", "query_id == 42"));
    ctx.push_obligation(ProofObligation::assume("ri", "response_id == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "matches == if query_id == response_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("matched", "matches == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response ID matches query ID");
}

#[test]
fn cname_chain_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["chain_length", "max_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("too_deep", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cl", "chain_length == 3"));
    ctx.push_obligation(ProofObligation::assume("md", "max_depth == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "td_def",
        "too_deep == if chain_length > max_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("not_too_deep", "too_deep == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CNAME chain 3 <= max depth 8");
}

#[test]
fn negative_cache_entry() {
    // NXDOMAIN cached for SOA minimum TTL
    let mut ctx = VerificationContext::new();
    for v in &["soa_minimum", "neg_ttl"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sm", "soa_minimum == 300"));
    ctx.push_obligation(ProofObligation::assume("nt_def", "neg_ttl == soa_minimum"));
    ctx.push_obligation(ProofObligation::assert("is_300", "neg_ttl == 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "negative cache TTL = SOA minimum 300s");
}

#[test]
fn truncation_flag_triggers_tcp() {
    let mut ctx = VerificationContext::new();
    for v in &["response_size", "max_udp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("truncated", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rs", "response_size == 600"));
    ctx.push_obligation(ProofObligation::assume("mu", "max_udp == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "truncated == if response_size > max_udp { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_truncated", "truncated == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "600 > 512 UDP max → truncated, use TCP");
}

#[test]
fn edns_buffer_size() {
    // EDNS0 extends UDP limit
    let mut ctx = VerificationContext::new();
    for v in &["default_udp", "edns_size", "effective_limit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("du", "default_udp == 512"));
    ctx.push_obligation(ProofObligation::assume("es", "edns_size == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "el_def",
        "effective_limit == if edns_size > default_udp { edns_size } else { default_udp }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_4096",
        "effective_limit == 4096",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EDNS0: effective UDP limit 4096 > 512");
}
