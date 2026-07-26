// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ipv4_header_min_length() {
    // Minimum IPv4 header: 20 bytes (IHL=5, 5*4=20)
    let mut ctx = VerificationContext::new();
    for v in &["ihl", "header_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ihl_val", "ihl == 5"));
    ctx.push_obligation(ProofObligation::assume("hl_def", "header_len == ihl * 4"));
    ctx.push_obligation(ProofObligation::assert("is_20", "header_len == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "IHL=5 → 20 byte header");
}

#[test]
fn ttl_decrements() {
    let mut ctx = VerificationContext::new();
    for v in &["ttl", "new_ttl"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("t", "ttl == 64"));
    ctx.push_obligation(ProofObligation::assume("nt_def", "new_ttl == ttl - 1"));
    ctx.push_obligation(ProofObligation::assert("is_63", "new_ttl == 63"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TTL: 64 → 63");
}

#[test]
fn ttl_zero_discard() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ttl", u32_ty());
    ctx.declare_var_typed("discard", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "ttl == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "discard == if ttl == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("must_discard", "discard == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TTL=0 → discard");
}

#[test]
fn total_length_includes_header() {
    let mut ctx = VerificationContext::new();
    for v in &["header_len", "payload_len", "total_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hl", "header_len == 20"));
    ctx.push_obligation(ProofObligation::assume("pl", "payload_len == 1480"));
    ctx.push_obligation(ProofObligation::assume(
        "tl_def",
        "total_len == header_len + payload_len",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1500", "total_len == 1500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "20 + 1480 = 1500 total");
}

#[test]
fn mtu_fragmentation_needed() {
    let mut ctx = VerificationContext::new();
    for v in &["packet_len", "mtu"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_frag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pl", "packet_len == 2000"));
    ctx.push_obligation(ProofObligation::assume("m", "mtu == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "nf_def",
        "needs_frag == if packet_len > mtu { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("frag", "needs_frag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2000 > 1500 → fragmentation needed");
}

#[test]
fn fragment_count() {
    // ceil(payload / (mtu - header)) fragments needed
    let mut ctx = VerificationContext::new();
    for v in &["payload", "mtu", "header", "max_payload", "fragments"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "payload == 4000"));
    ctx.push_obligation(ProofObligation::assume("m", "mtu == 1500"));
    ctx.push_obligation(ProofObligation::assume("h", "header == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "mp_def",
        "max_payload == mtu - header",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fragments == (payload + max_payload - 1) / max_payload",
    ));
    // max_payload = 1480; (4000 + 1479) / 1480 = 5479/1480 = 3
    ctx.push_obligation(ProofObligation::assert("is_3", "fragments == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "4000 bytes → 3 fragments");
}

#[test]
fn port_number_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("port", u32_ty());
    ctx.declare_var_typed("is_well_known", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "port == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "wk_def",
        "is_well_known == if port < 1024 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("well_known", "is_well_known == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "port 80 is well-known");
}

#[test]
fn tcp_sequence_wrap() {
    // TCP sequence numbers are 32-bit, wrap around
    let mut ctx = VerificationContext::new();
    for v in &["seq", "payload_len", "next_seq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "seq == 4294967290")); // near MAX
    ctx.push_obligation(ProofObligation::assume("pl", "payload_len == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "next_seq == seq + payload_len",
    ));
    // 4294967290 + 10 = 4294967300; wraps to 4 in u32
    ctx.push_obligation(ProofObligation::assert("wrapped", "next_seq == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "TCP seq wrap: near MAX + 10 wraps to 4");
}

#[test]
fn checksum_complement() {
    // One's complement sum: a + complement(a) = all 1s
    let mut ctx = VerificationContext::new();
    for v in &["data", "complement", "sum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d", "data == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "complement == 65535 - data",
    ));
    ctx.push_obligation(ProofObligation::assume("s_def", "sum == data + complement"));
    ctx.push_obligation(ProofObligation::assert("all_ones", "sum == 65535"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "42 + (65535-42) = 65535");
}

#[test]
fn ethernet_frame_min_size() {
    // Minimum Ethernet frame: 64 bytes (14 header + 46 payload + 4 FCS)
    let mut ctx = VerificationContext::new();
    for v in &["header", "min_payload", "fcs", "min_frame"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "header == 14"));
    ctx.push_obligation(ProofObligation::assume("mp", "min_payload == 46"));
    ctx.push_obligation(ProofObligation::assume("f", "fcs == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "mf_def",
        "min_frame == header + min_payload + fcs",
    ));
    ctx.push_obligation(ProofObligation::assert("is_64", "min_frame == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "14 + 46 + 4 = 64 byte min frame");
}
