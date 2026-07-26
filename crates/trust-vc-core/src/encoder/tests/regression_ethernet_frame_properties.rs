// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn minimum_frame_size() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "payload_size",
        "header_size",
        "fcs_size",
        "total_size",
        "min_frame",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "payload_size == 46")); // minimum payload
    ctx.push_obligation(ProofObligation::assume("hs", "header_size == 14")); // dst+src+type
    ctx.push_obligation(ProofObligation::assume("fs", "fcs_size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "ts_def",
        "total_size == header_size + payload_size + fcs_size",
    ));
    ctx.push_obligation(ProofObligation::assume("mf", "min_frame == 64"));
    ctx.push_obligation(ProofObligation::assert(
        "meets_min",
        "total_size == min_frame",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min frame: 14+46+4 = 64 bytes");
}

#[test]
fn maximum_frame_size_mtu() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "payload_size",
        "header_size",
        "fcs_size",
        "total_size",
        "max_frame",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "payload_size == 1500")); // standard MTU
    ctx.push_obligation(ProofObligation::assume("hs", "header_size == 14"));
    ctx.push_obligation(ProofObligation::assume("fs", "fcs_size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "ts_def",
        "total_size == header_size + payload_size + fcs_size",
    ));
    ctx.push_obligation(ProofObligation::assume("mxf", "max_frame == 1518"));
    ctx.push_obligation(ProofObligation::assert(
        "meets_max",
        "total_size == max_frame",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max frame: 14+1500+4 = 1518 bytes");
}

#[test]
fn vlan_tag_adds_four_bytes() {
    let mut ctx = VerificationContext::new();
    for v in &["untagged_size", "vlan_tag_size", "tagged_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("us", "untagged_size == 1518"));
    ctx.push_obligation(ProofObligation::assume("vt", "vlan_tag_size == 4")); // 802.1Q
    ctx.push_obligation(ProofObligation::assume(
        "ts_def",
        "tagged_size == untagged_size + vlan_tag_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1522", "tagged_size == 1522"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "VLAN tag: 1518 + 4 = 1522 bytes");
}

#[test]
fn jumbo_frame_size() {
    let mut ctx = VerificationContext::new();
    for v in &["payload_size", "header_size", "fcs_size", "total_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "payload_size == 9000")); // jumbo MTU
    ctx.push_obligation(ProofObligation::assume("hs", "header_size == 14"));
    ctx.push_obligation(ProofObligation::assume("fs", "fcs_size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "ts_def",
        "total_size == header_size + payload_size + fcs_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_9018", "total_size == 9018"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "jumbo: 14+9000+4 = 9018 bytes");
}

#[test]
fn interframe_gap() {
    let mut ctx = VerificationContext::new();
    for v in &["frame_size", "gap_bytes", "wire_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fs", "frame_size == 64"));
    ctx.push_obligation(ProofObligation::assume("gb", "gap_bytes == 12")); // 96 bits = 12 bytes
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "wire_bytes == frame_size + gap_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_76", "wire_bytes == 76"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wire: 64 frame + 12 IFG = 76 bytes");
}

#[test]
fn preamble_overhead() {
    let mut ctx = VerificationContext::new();
    for v in &["preamble_size", "sfd_size", "frame_size", "total_wire"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "preamble_size == 7"));
    ctx.push_obligation(ProofObligation::assume("ss", "sfd_size == 1"));
    ctx.push_obligation(ProofObligation::assume("fs", "frame_size == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "tw_def",
        "total_wire == preamble_size + sfd_size + frame_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_72", "total_wire == 72"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "preamble: 7+1+64 = 72 bytes on wire");
}

#[test]
fn throughput_with_overhead() {
    let mut ctx = VerificationContext::new();
    for v in &["payload", "overhead", "total_per_frame", "efficiency_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "payload == 1500"));
    ctx.push_obligation(ProofObligation::assume("o", "overhead == 38")); // 14 hdr + 4 FCS + 7 pre + 1 SFD + 12 IFG
    ctx.push_obligation(ProofObligation::assume(
        "tpf_def",
        "total_per_frame == payload + overhead",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "efficiency_pct == payload * 100 / total_per_frame",
    ));
    ctx.push_obligation(ProofObligation::assert("is_97", "efficiency_pct == 97")); // 1500/1538 ≈ 97%
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "efficiency: 1500*100/1538 ≈ 97%");
}

#[test]
fn mac_address_size() {
    let mut ctx = VerificationContext::new();
    for v in &["dst_mac_bytes", "src_mac_bytes", "total_mac"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("dm", "dst_mac_bytes == 6"));
    ctx.push_obligation(ProofObligation::assume("sm", "src_mac_bytes == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "tm_def",
        "total_mac == dst_mac_bytes + src_mac_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_12", "total_mac == 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MAC: 6 dst + 6 src = 12 bytes");
}

#[test]
fn padding_for_minimum_frame() {
    let mut ctx = VerificationContext::new();
    for v in &["data_size", "min_payload", "padding_needed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ds", "data_size == 20")); // small packet
    ctx.push_obligation(ProofObligation::assume("mp", "min_payload == 46"));
    ctx.push_obligation(ProofObligation::assume(
        "pn_def",
        "padding_needed == if data_size < min_payload { min_payload - data_size } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_26", "padding_needed == 26"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "padding: 46 - 20 = 26 bytes needed");
}

#[test]
fn double_vlan_tag_qinq() {
    let mut ctx = VerificationContext::new();
    for v in &["base_frame", "outer_tag", "inner_tag", "total_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bf", "base_frame == 1518"));
    ctx.push_obligation(ProofObligation::assume("ot", "outer_tag == 4"));
    ctx.push_obligation(ProofObligation::assume("it", "inner_tag == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "ts_def",
        "total_size == base_frame + outer_tag + inner_tag",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1526", "total_size == 1526"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QinQ: 1518 + 4 + 4 = 1526 bytes");
}
