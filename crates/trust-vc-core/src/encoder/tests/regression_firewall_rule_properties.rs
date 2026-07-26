// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn port_range_match() {
    let mut ctx = VerificationContext::new();
    for v in &["packet_port", "rule_port_low", "rule_port_high"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("matches", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pp", "packet_port == 8080"));
    ctx.push_obligation(ProofObligation::assume("rpl", "rule_port_low == 8000"));
    ctx.push_obligation(ProofObligation::assume("rph", "rule_port_high == 9000"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "matches == if packet_port >= rule_port_low && packet_port <= rule_port_high { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "matches == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "firewall: port 8080 in [8000, 9000] → match");
}

#[test]
fn ip_subnet_match() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "packet_ip",
        "subnet_base",
        "subnet_mask",
        "masked_packet",
        "masked_subnet",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_subnet", i32_ty());
    // 192.168.1.100 & 255.255.255.0 == 192.168.1.0
    // Precompute: both mask to same value
    ctx.push_obligation(ProofObligation::assume("pi", "packet_ip == 3232235876")); // 192.168.1.100
    ctx.push_obligation(ProofObligation::assume("sb", "subnet_base == 3232235776")); // 192.168.1.0
    ctx.push_obligation(ProofObligation::assume("mp", "masked_packet == 3232235776")); // precomputed
    ctx.push_obligation(ProofObligation::assume("ms", "masked_subnet == 3232235776")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "in_subnet == if masked_packet == masked_subnet { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_subnet == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "firewall: 192.168.1.100 in 192.168.1.0/24");
}

#[test]
fn rule_priority_ordering() {
    let mut ctx = VerificationContext::new();
    for v in &["rule_a_priority", "rule_b_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("a_wins", i32_ty());
    // Lower priority number = higher precedence
    ctx.push_obligation(ProofObligation::assume("rap", "rule_a_priority == 10"));
    ctx.push_obligation(ProofObligation::assume("rbp", "rule_b_priority == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "aw_def",
        "a_wins == if rule_a_priority < rule_b_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "a_wins == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "firewall: priority 10 < 20 → rule A wins");
}

#[test]
fn connection_tracking_timeout() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "last_packet_time",
        "current_time",
        "timeout_seconds",
        "idle_seconds",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("expired", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lpt", "last_packet_time == 1000"));
    ctx.push_obligation(ProofObligation::assume("ct", "current_time == 1400"));
    ctx.push_obligation(ProofObligation::assume("ts", "timeout_seconds == 300")); // 5 min
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "idle_seconds == current_time - last_packet_time",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "expired == if idle_seconds > timeout_seconds { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_400", "idle_seconds == 400"));
    ctx.push_obligation(ProofObligation::assert("yes", "expired == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "firewall conntrack: 400s idle > 300s timeout → expired",
    );
}

#[test]
fn rate_limit_token_bucket() {
    let mut ctx = VerificationContext::new();
    for v in &["tokens", "packet_cost", "remaining_tokens"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("allowed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "tokens == 100"));
    ctx.push_obligation(ProofObligation::assume("pc", "packet_cost == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "allowed == if tokens >= packet_cost { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "rt_def",
        "remaining_tokens == if tokens >= packet_cost { tokens - packet_cost } else { tokens }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "allowed == 1"));
    ctx.push_obligation(ProofObligation::assert("is_90", "remaining_tokens == 90"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "firewall rate limit: 100 tokens - 10 cost = 90 remaining",
    );
}

#[test]
fn stateful_tcp_tracking() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("syn_flag", u32_ty());
    ctx.declare_var_typed("ack_flag", u32_ty());
    ctx.declare_var_typed("connection_state", u32_ty());
    ctx.declare_var_typed("allow_packet", i32_ty());
    // State 0=none, 1=syn_sent, 2=established
    // SYN+ACK in syn_sent → established
    ctx.push_obligation(ProofObligation::assume("sf", "syn_flag == 1"));
    ctx.push_obligation(ProofObligation::assume("af", "ack_flag == 1"));
    ctx.push_obligation(ProofObligation::assume("cs", "connection_state == 1")); // syn_sent
    ctx.push_obligation(ProofObligation::assume(
        "ap_def",
        "allow_packet == if connection_state == 1 && syn_flag == 1 && ack_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "allow_packet == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "firewall stateful: SYN+ACK in syn_sent → allow");
}

#[test]
fn nat_port_translation() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "internal_port",
        "external_port_base",
        "connection_index",
        "external_port",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("port_valid", i32_ty());
    // NAT: external_port = base + connection_index
    ctx.push_obligation(ProofObligation::assume("ip", "internal_port == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "epb",
        "external_port_base == 49152",
    ));
    ctx.push_obligation(ProofObligation::assume("ci", "connection_index == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "external_port == external_port_base + connection_index",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "pv_def",
        "port_valid == if external_port <= 65535 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_49194",
        "external_port == 49194",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "port_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "firewall NAT: 49152 + 42 = 49194 (valid port)");
}

#[test]
fn acl_rule_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ingress_rules", "egress_rules", "total_rules", "max_rules"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ir", "ingress_rules == 50"));
    ctx.push_obligation(ProofObligation::assume("er", "egress_rules == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "tr_def",
        "total_rules == ingress_rules + egress_rules",
    ));
    ctx.push_obligation(ProofObligation::assume("mr", "max_rules == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if total_rules <= max_rules { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "total_rules == 80"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "firewall ACL: 50 + 30 = 80 rules ≤ 256 max");
}

#[test]
fn geo_ip_block() {
    let mut ctx = VerificationContext::new();
    for v in &["ip_country_code", "blocked_country"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("blocked", i32_ty());
    // Country code match → block
    ctx.push_obligation(ProofObligation::assume("icc", "ip_country_code == 42"));
    ctx.push_obligation(ProofObligation::assume("bc", "blocked_country == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "blocked == if ip_country_code == blocked_country { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "blocked == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "firewall geo-IP: country 42 matches block list");
}

#[test]
fn packet_fragment_reassembly() {
    let mut ctx = VerificationContext::new();
    for v in &["fragment_offset", "fragment_length", "total_length"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("complete", i32_ty());
    // Last fragment: offset + length >= total_length
    ctx.push_obligation(ProofObligation::assume("fo", "fragment_offset == 1400"));
    ctx.push_obligation(ProofObligation::assume("fl", "fragment_length == 200"));
    ctx.push_obligation(ProofObligation::assume("tl", "total_length == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "complete == if fragment_offset + fragment_length >= total_length { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "complete == 1")); // 1400 + 200 = 1600 >= 1500
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "firewall: fragment 1400+200 >= 1500 → reassembly complete",
    );
}
