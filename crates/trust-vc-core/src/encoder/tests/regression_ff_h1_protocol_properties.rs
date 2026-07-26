// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn device_address() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "max_address"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("addr_ok", i32_ty());
    // FF H1 device address (16-247, 0-15 reserved, 248-255 reserved)
    ctx.push_obligation(ProofObligation::assume("a", "address == 32"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_address == 247"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "addr_ok == if address >= 16 && address <= max_address { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "addr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FF H1: address 32 in [16, 247] → OK");
}

#[test]
fn segment_length() {
    let mut ctx = VerificationContext::new();
    for v in &["seg_m", "max_seg_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("seg_ok", i32_ty());
    // H1 segment length in meters
    ctx.push_obligation(ProofObligation::assume("sm", "seg_m == 800"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_seg_m == 1900")); // 1900m max
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "seg_ok == if seg_m <= max_seg_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "seg_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FF H1: 800m segment ≤ 1900m max → OK");
}

#[test]
fn devices_per_segment() {
    let mut ctx = VerificationContext::new();
    for v in &["devices", "max_devices"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dev_ok", i32_ty());
    // Maximum devices per H1 segment
    ctx.push_obligation(ProofObligation::assume("d", "devices == 16"));
    ctx.push_obligation(ProofObligation::assume("md", "max_devices == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dev_ok == if devices >= 1 && devices <= max_devices { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dev_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FF H1: 16 devices in [1, 32] → OK");
}

#[test]
fn macrocycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["macro_ms", "min_macro_ms", "max_macro_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mc_ok", i32_ty());
    // Macrocycle time in milliseconds
    ctx.push_obligation(ProofObligation::assume("mm", "macro_ms == 500"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_macro_ms == 50"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_macro_ms == 30000"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mc_ok == if macro_ms >= min_macro_ms && macro_ms <= max_macro_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FF H1: 500ms macrocycle in [50, 30000] → OK");
}

#[test]
fn function_block_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fb_type", u32_ty());
    ctx.declare_var_typed("valid_fb", i32_ty());
    // Standard function blocks: 1=AI, 2=AO, 3=DI, 4=DO, 5=PID, 6=Selector
    ctx.push_obligation(ProofObligation::assume("ft", "fb_type == 5")); // PID
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_fb == if fb_type == 1 || fb_type == 2 || fb_type == 3 || fb_type == 4 || fb_type == 5 || fb_type == 6 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_fb == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FF H1: PID is valid function block type");
}

#[test]
fn schedule_slots() {
    let mut ctx = VerificationContext::new();
    for v in &["slots", "max_slots"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("slot_ok", i32_ty());
    // Number of scheduled communication slots per macrocycle
    ctx.push_obligation(ProofObligation::assume("s", "slots == 8"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_slots == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "slot_ok == if slots >= 1 && slots <= max_slots { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "slot_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FF H1: 8 schedule slots in [1, 64] → OK");
}

#[test]
fn data_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_kbps", u32_ty());
    ctx.declare_var_typed("valid_rate", i32_ty());
    // FF H1 fixed data rate (always 31.25 kbps, encoded as 31)
    ctx.push_obligation(ProofObligation::assume("rk", "rate_kbps == 31"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_rate == if rate_kbps == 31 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_rate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FF H1: 31.25 kbps is valid (only) data rate");
}

#[test]
fn vfd_tag_length() {
    let mut ctx = VerificationContext::new();
    for v in &["tag_len", "max_tag_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tag_ok", i32_ty());
    // Virtual Field Device tag name length
    ctx.push_obligation(ProofObligation::assume("tl", "tag_len == 16"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tag_len == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tag_ok == if tag_len >= 1 && tag_len <= max_tag_len { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tag_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FF H1: 16-char VFD tag in [1, 32] → OK");
}

#[test]
fn link_master_count() {
    let mut ctx = VerificationContext::new();
    for v in &["masters", "min_masters", "max_masters"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lm_ok", i32_ty());
    // Link Active Schedulers (LAS) per segment
    ctx.push_obligation(ProofObligation::assume("m", "masters == 2"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_masters == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_masters == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lm_ok == if masters >= min_masters && masters <= max_masters { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "lm_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FF H1: 2 link masters in [1, 4] → OK");
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "min_supply_mv", "max_supply_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sup_ok", i32_ty());
    // H1 bus supply voltage in mV (9-32V DC)
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 24000")); // 24V
    ctx.push_obligation(ProofObligation::assume("mn", "min_supply_mv == 9000")); // 9V
    ctx.push_obligation(ProofObligation::assume("mx", "max_supply_mv == 32000")); // 32V
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sup_ok == if supply_mv >= min_supply_mv && supply_mv <= max_supply_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sup_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FF H1: 24V supply in [9, 32] → OK");
}
