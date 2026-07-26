// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn tag_uid_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("uid_bytes", u32_ty());
    ctx.declare_var_typed("is_double_size", i32_ty());
    // NFC-A UID: single (4), double (7), or triple (10) bytes
    ctx.push_obligation(ProofObligation::assume("ub", "uid_bytes == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "id_def",
        "is_double_size == if uid_bytes == 7 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_double_size == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NFC: 7-byte UID → double size");
}

#[test]
fn carrier_frequency() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_khz", u32_ty());
    ctx.declare_var_typed("is_hf", i32_ty());
    // HF RFID/NFC: 13560 kHz (13.56 MHz)
    ctx.push_obligation(ProofObligation::assume("fk", "freq_khz == 13560"));
    ctx.push_obligation(ProofObligation::assume(
        "ih_def",
        "is_hf == if freq_khz == 13560 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_hf == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NFC: 13560 kHz = 13.56 MHz → HF band");
}

#[test]
fn ndef_message_size() {
    let mut ctx = VerificationContext::new();
    for v in &["payload_bytes", "header_bytes", "total_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits_tag", i32_ty());
    // NDEF record: header + payload. Tag capacity e.g. 888 bytes (NTAG216)
    ctx.push_obligation(ProofObligation::assume("pb", "payload_bytes == 800"));
    ctx.push_obligation(ProofObligation::assume("hb", "header_bytes == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bytes == payload_bytes + header_bytes",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ft_def",
        "fits_tag == if total_bytes <= 888 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_807", "total_bytes == 807"));
    ctx.push_obligation(ProofObligation::assert("yes", "fits_tag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NFC: 800 + 7 = 807 ≤ 888 tag capacity → fits");
}

#[test]
fn read_range_check() {
    let mut ctx = VerificationContext::new();
    for v in &["block_addr", "max_block"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("addr_valid", i32_ty());
    // MIFARE Classic: 64 blocks (0-63) for 1K card
    ctx.push_obligation(ProofObligation::assume("ba", "block_addr == 42"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_block == 63"));
    ctx.push_obligation(ProofObligation::assume(
        "av_def",
        "addr_valid == if block_addr <= max_block { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "NFC: block 42 ≤ 63 max → valid MIFARE Classic address",
    );
}

#[test]
fn sector_trailer_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("block_in_sector", u32_ty());
    ctx.declare_var_typed("is_trailer", i32_ty());
    // MIFARE Classic: each sector has 4 blocks, block 3 is the sector trailer
    ctx.push_obligation(ProofObligation::assume("bs", "block_in_sector == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "it_def",
        "is_trailer == if block_in_sector == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_trailer == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NFC: block 3 in sector → sector trailer");
}

#[test]
fn anti_collision_level() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cascade_level", u32_ty());
    ctx.declare_var_typed("needs_more", i32_ty());
    // Anti-collision: cascade levels 1-3 for UID resolution
    ctx.push_obligation(ProofObligation::assume("cl", "cascade_level == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "nm_def",
        "needs_more == if cascade_level < 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_more == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "NFC: cascade level 2 < 3 → needs more anti-collision",
    );
}

#[test]
fn data_rate_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_kbps", u32_ty());
    ctx.declare_var_typed("is_fast", i32_ty());
    // NFC: 106, 212, 424, 848 kbps. Fast = 424+ kbps
    ctx.push_obligation(ProofObligation::assume("rk", "rate_kbps == 424"));
    ctx.push_obligation(ProofObligation::assume(
        "if_def",
        "is_fast == if rate_kbps >= 424 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_fast == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NFC: 424 kbps ≥ 424 → fast data rate");
}

#[test]
fn authentication_key_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("key_type", u32_ty());
    ctx.declare_var_typed("is_key_a", i32_ty());
    // MIFARE: key A = 0x60, key B = 0x61
    ctx.push_obligation(ProofObligation::assume("kt", "key_type == 96")); // 0x60
    ctx.push_obligation(ProofObligation::assume(
        "ika_def",
        "is_key_a == if key_type == 96 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_key_a == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NFC: key type 0x60 → MIFARE Key A");
}

#[test]
fn tag_memory_pages() {
    let mut ctx = VerificationContext::new();
    for v in &["total_pages", "bytes_per_page"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("total_bytes", u32_ty());
    // NTAG215: 135 pages × 4 bytes = 540 bytes. Precompute.
    ctx.push_obligation(ProofObligation::assume("tp", "total_pages == 135"));
    ctx.push_obligation(ProofObligation::assume("bp", "bytes_per_page == 4"));
    ctx.push_obligation(ProofObligation::assume("tb", "total_bytes == 540")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_540", "total_bytes == 540"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "NFC: NTAG215 135 pages × 4 = 540 bytes (precomputed)",
    );
}

#[test]
fn field_strength() {
    let mut ctx = VerificationContext::new();
    for v in &["field_strength_ma_m", "min_field_ma_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_power_tag", i32_ty());
    // Minimum field strength to power passive tag: ~1500 mA/m (1.5 A/m)
    ctx.push_obligation(ProofObligation::assume("fs", "field_strength_ma_m == 2000"));
    ctx.push_obligation(ProofObligation::assume("mf", "min_field_ma_m == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "cp_def",
        "can_power_tag == if field_strength_ma_m >= min_field_ma_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_power_tag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NFC: 2000 mA/m ≥ 1500 min → can power passive tag");
}
