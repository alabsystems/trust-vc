// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn query_id_match() {
    let mut ctx = VerificationContext::new();
    for v in &["request_id", "response_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("id_match", i32_ty());
    // DNS: response ID must match request ID (anti-spoofing)
    ctx.push_obligation(ProofObligation::assume("ri", "request_id == 54321"));
    ctx.push_obligation(ProofObligation::assume("rsi", "response_id == 54321"));
    ctx.push_obligation(ProofObligation::assume(
        "im_def",
        "id_match == if request_id == response_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "id_match == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNS: response ID 54321 matches request → valid");
}

#[test]
fn ttl_expiry_check() {
    let mut ctx = VerificationContext::new();
    for v in &["cached_at", "ttl_seconds", "current_time", "expiry_time"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("expired", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ca", "cached_at == 1000"));
    ctx.push_obligation(ProofObligation::assume("ts", "ttl_seconds == 300"));
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 1400"));
    ctx.push_obligation(ProofObligation::assume(
        "et_def",
        "expiry_time == cached_at + ttl_seconds",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "expired == if current_time >= expiry_time { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1300", "expiry_time == 1300"));
    ctx.push_obligation(ProofObligation::assert("yes", "expired == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DNS: cached@1000 + TTL 300 = 1300, now 1400 → expired",
    );
}

#[test]
fn cache_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["cached_entries", "max_cache_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cache_full", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ce", "cached_entries == 9500"));
    ctx.push_obligation(ProofObligation::assume("mce", "max_cache_entries == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "cf_def",
        "cache_full == if cached_entries >= max_cache_entries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "cache_full == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNS cache: 9500 entries < 10000 max → not full");
}

#[test]
fn rcode_interpretation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rcode", u32_ty());
    ctx.declare_var_typed("is_nxdomain", i32_ty());
    ctx.declare_var_typed("is_noerror", i32_ty());
    // RCODE 0 = NOERROR, 3 = NXDOMAIN
    ctx.push_obligation(ProofObligation::assume("rc", "rcode == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "inx_def",
        "is_nxdomain == if rcode == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ine_def",
        "is_noerror == if rcode == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("nxdomain", "is_nxdomain == 1"));
    ctx.push_obligation(ProofObligation::assert("not_noerror", "is_noerror == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNS: RCODE 3 → NXDOMAIN, not NOERROR");
}

#[test]
fn recursion_depth_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["current_depth", "max_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_recurse", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cd", "current_depth == 8"));
    ctx.push_obligation(ProofObligation::assume("md", "max_depth == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "cr_def",
        "can_recurse == if current_depth < max_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_recurse == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNS: recursion depth 8 < 10 max → can recurse");
}

#[test]
fn message_size_limit() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "header_bytes",
        "question_bytes",
        "answer_bytes",
        "total_bytes",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_udp_limit", i32_ty());
    // DNS over UDP: max 512 bytes (without EDNS)
    ctx.push_obligation(ProofObligation::assume("hb", "header_bytes == 12"));
    ctx.push_obligation(ProofObligation::assume("qb", "question_bytes == 30"));
    ctx.push_obligation(ProofObligation::assume("ab", "answer_bytes == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bytes == header_bytes + question_bytes + answer_bytes",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "wu_def",
        "within_udp_limit == if total_bytes <= 512 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_242", "total_bytes == 242"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_udp_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNS: 12+30+200 = 242 bytes ≤ 512 UDP limit");
}

#[test]
fn cname_chain_length() {
    let mut ctx = VerificationContext::new();
    for v in &["chain_length", "max_chain"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("too_long", i32_ty());
    // Prevent infinite CNAME chains
    ctx.push_obligation(ProofObligation::assume("cl", "chain_length == 12"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_chain == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "tl_def",
        "too_long == if chain_length > max_chain { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "too_long == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNS: CNAME chain 12 > 8 max → reject");
}

#[test]
fn edns_buffer_size() {
    let mut ctx = VerificationContext::new();
    for v in &["advertised_size", "min_edns_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("supports_large", i32_ty());
    // EDNS0: advertised UDP buffer size, typically 4096
    ctx.push_obligation(ProofObligation::assume("as", "advertised_size == 4096"));
    ctx.push_obligation(ProofObligation::assume("mes", "min_edns_size == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "sl_def",
        "supports_large == if advertised_size > min_edns_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "supports_large == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNS EDNS0: 4096 > 512 → supports large responses");
}

#[test]
fn negative_cache_ttl() {
    let mut ctx = VerificationContext::new();
    for v in &["soa_minimum_ttl", "max_negative_ttl"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("effective_ttl", u32_ty());
    // Negative cache TTL = min(SOA minimum, configured max)
    ctx.push_obligation(ProofObligation::assume("smt", "soa_minimum_ttl == 600"));
    ctx.push_obligation(ProofObligation::assume("mnt", "max_negative_ttl == 3600"));
    ctx.push_obligation(ProofObligation::assume(
        "et_def",
        "effective_ttl == if soa_minimum_ttl < max_negative_ttl { soa_minimum_ttl } else { max_negative_ttl }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_600", "effective_ttl == 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNS negative: min(600 SOA, 3600 max) = 600s TTL");
}

#[test]
fn query_rate_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["queries_this_second", "rate_limit_qps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("throttled", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "qts",
        "queries_this_second == 1200",
    ));
    ctx.push_obligation(ProofObligation::assume("rlq", "rate_limit_qps == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "throttled == if queries_this_second > rate_limit_qps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "throttled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DNS: 1200 qps > 1000 limit → throttled");
}
