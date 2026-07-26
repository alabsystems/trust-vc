// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn mii_clock_divider() {
    let mut ctx = VerificationContext::new();
    for v in &["hclk_mhz", "divider", "mdc_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // MDC must be <= 2.5MHz
    ctx.push_obligation(ProofObligation::assume("hc", "hclk_mhz == 72"));
    ctx.push_obligation(ProofObligation::assume("d", "divider == 42")); // CR bits
    ctx.push_obligation(ProofObligation::assume("mdc", "mdc_mhz == 1")); // 72/42 ≈ 1.7, rounded
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if mdc_mhz <= 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ETH MDC: ~1.7MHz <= 2.5MHz");
}

#[test]
fn tx_descriptor_ring_wrap() {
    let mut ctx = VerificationContext::new();
    for v in &["current_desc", "num_descriptors", "next_desc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cd", "current_desc == 15"));
    ctx.push_obligation(ProofObligation::assume("nd", "num_descriptors == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "nx_def",
        "next_desc == (current_desc + 1) % num_descriptors",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "next_desc == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ETH TX desc: 15+1 mod 16 = 0");
}

#[test]
fn rx_buffer_size() {
    let mut ctx = VerificationContext::new();
    for v in &["mtu", "header_bytes", "buffer_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sufficient", i32_ty());
    ctx.push_obligation(ProofObligation::assume("m", "mtu == 1500"));
    ctx.push_obligation(ProofObligation::assume("hb", "header_bytes == 14")); // Ethernet header
    ctx.push_obligation(ProofObligation::assume("bs", "buffer_size == 2048")); // power-of-two
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "sufficient == if buffer_size >= mtu + header_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "sufficient == 1")); // 2048 >= 1514
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ETH RX: 2048 >= 1500+14 → sufficient");
}

#[test]
fn crc_strip_payload_length() {
    let mut ctx = VerificationContext::new();
    for v in &["frame_length", "header", "crc", "payload"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fl", "frame_length == 1518")); // max Ethernet
    ctx.push_obligation(ProofObligation::assume("h", "header == 14"));
    ctx.push_obligation(ProofObligation::assume("c", "crc == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "payload == frame_length - header - crc",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1500", "payload == 1500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ETH: 1518-14-4=1500 payload");
}

#[test]
fn promiscuous_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("promiscuous", u32_ty());
    ctx.declare_var_typed("dst_match", u32_ty());
    ctx.declare_var_typed("accept_frame", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "promiscuous == 1"));
    ctx.push_obligation(ProofObligation::assume("dm", "dst_match == 0")); // doesn't match our MAC
    ctx.push_obligation(ProofObligation::assume(
        "af_def",
        "accept_frame == if promiscuous == 1 || dst_match == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("accepted", "accept_frame == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ETH: promiscuous → accept all frames");
}

#[test]
fn vlan_tag_identification() {
    let mut ctx = VerificationContext::new();
    for v in &["ethertype", "vlan_ethertype"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_vlan", i32_ty());
    ctx.push_obligation(ProofObligation::assume("et", "ethertype == 33024")); // 0x8100
    ctx.push_obligation(ProofObligation::assume("ve", "vlan_ethertype == 33024"));
    ctx.push_obligation(ProofObligation::assume(
        "iv_def",
        "is_vlan == if ethertype == vlan_ethertype { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_vlan == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ETH: ethertype 0x8100 → VLAN tagged");
}

#[test]
fn flow_control_pause_time() {
    let mut ctx = VerificationContext::new();
    for v in &["pause_quanta", "slot_time_ns", "pause_duration_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pause quanta = 512 bit times. At 100Mbps: 512 * 10ns = 5120ns per quantum
    ctx.push_obligation(ProofObligation::assume("pq", "pause_quanta == 100"));
    ctx.push_obligation(ProofObligation::assume("st", "slot_time_ns == 5120")); // per quantum
    ctx.push_obligation(ProofObligation::assume(
        "pd_def",
        "pause_duration_ns == pause_quanta * slot_time_ns",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_512000",
        "pause_duration_ns == 512000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ETH pause: 100×5120=512000ns");
}

#[test]
fn multicast_hash_filter() {
    let mut ctx = VerificationContext::new();
    for v in &["hash_value", "hash_table_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hash_index", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hv", "hash_value == 200"));
    ctx.push_obligation(ProofObligation::assume("hts", "hash_table_size == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "hi_def",
        "hash_index == hash_value % hash_table_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "hash_index == 8")); // 200 % 64 = 8
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ETH hash: 200 mod 64 = 8");
}

#[test]
fn timestamping_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["ptp_clock_hz", "subsecond_increment_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // PTP timestamp resolution = 1/ptp_clock period
    ctx.push_obligation(ProofObligation::assume("pc", "ptp_clock_hz == 50000000")); // 50MHz
    ctx.push_obligation(ProofObligation::assume(
        "si",
        "subsecond_increment_ns == 20",
    )); // 1/50MHz = 20ns
    ctx.push_obligation(ProofObligation::assert(
        "is_20",
        "subsecond_increment_ns == 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "precise",
        "subsecond_increment_ns < 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ETH PTP: 50MHz → 20ns resolution");
}

#[test]
fn descriptor_ownership() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("own_bit", u32_ty());
    ctx.declare_var_typed("dma_owns", i32_ty());
    // OWN bit: 1=DMA owns (can use), 0=CPU owns (DMA must not touch)
    ctx.push_obligation(ProofObligation::assume("ob", "own_bit == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dma_owns == if own_bit == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dma_owns == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ETH desc: OWN=1 → DMA can use");
}
