// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn update_rate_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["update_rate", "min_rate", "max_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // OPC DA update rate in ms, bounded 1-60000
    ctx.push_obligation(ProofObligation::assume("ur", "update_rate == 1000")); // 1 second
    ctx.push_obligation(ProofObligation::assume("mn", "min_rate == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rate == 60000"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if update_rate >= min_rate && update_rate <= max_rate { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: 1 <= 1000 <= 60000 ms update rate");
}

#[test]
fn item_count_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["item_count", "max_items"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_limit", i32_ty());
    // OPC DA group can hold 1-100000 items
    ctx.push_obligation(ProofObligation::assume("ic", "item_count == 5000"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_items == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_limit == if item_count >= 1 && item_count <= max_items { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "within_limit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: 1 <= 5000 <= 100000 items");
}

#[test]
fn group_count_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["group_count", "max_groups"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // OPC DA server supports 1-256 groups
    ctx.push_obligation(ProofObligation::assume("gc", "group_count == 32"));
    ctx.push_obligation(ProofObligation::assume("mg", "max_groups == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if group_count >= 1 && group_count <= max_groups { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: 1 <= 32 <= 256 groups");
}

#[test]
fn data_type_five_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("data_type", u32_ty());
    ctx.declare_var_typed("is_vt_r8", i32_ty());
    // VARIANT types: 1=VT_BOOL, 2=VT_I4, 3=VT_R4, 4=VT_R8, 5=VT_BSTR
    ctx.push_obligation(ProofObligation::assume("dt", "data_type == 4")); // VT_R8 (double)
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_vt_r8 == if data_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "data_type >= 1 && data_type <= 5",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "is_vt_r8 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: data_type=4 (VT_R8) in 1..5");
}

#[test]
fn quality_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("quality", u32_ty());
    ctx.declare_var_typed("is_good", i32_ty());
    // Quality: 1=good, 2=bad, 3=uncertain
    ctx.push_obligation(ProofObligation::assume("ql", "quality == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ig_def",
        "is_good == if quality == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "quality >= 1 && quality <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "is_good == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: quality=1 (good) in 1..3");
}

#[test]
fn dead_band_percentage() {
    let mut ctx = VerificationContext::new();
    for v in &["dead_band", "max_dead_band", "effective_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // Dead band ×100 %: 0-10000 (0.00%-100.00%). effective_pct = dead_band / 100
    ctx.push_obligation(ProofObligation::assume("db", "dead_band == 500")); // 5.00%
    ctx.push_obligation(ProofObligation::assume("md", "max_dead_band == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "effective_pct == dead_band / 100",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if dead_band <= max_dead_band { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "effective_pct == 5"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "OPC DA: dead_band=500 → 5%, <= 10000");
}

#[test]
fn subscription_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("subscription_mode", u32_ty());
    ctx.declare_var_typed("is_async", i32_ty());
    // 1=synchronous read, 2=asynchronous, 3=callback
    ctx.push_obligation(ProofObligation::assume("sm", "subscription_mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "is_async == if subscription_mode == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "subscription_mode >= 1 && subscription_mode <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "is_async == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: subscription_mode=2 (async) in 1..3");
}

#[test]
fn cache_enabled_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cache_enabled", i32_ty());
    ctx.declare_var_typed("reads_from_cache", i32_ty());
    // Boolean flag: 1=from cache, 0=from device
    ctx.push_obligation(ProofObligation::assume("ce", "cache_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "rc_def",
        "reads_from_cache == if cache_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_bool",
        "cache_enabled == 0 || cache_enabled == 1",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "reads_from_cache == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: cache_enabled=1 → reads from cache");
}

#[test]
fn browse_depth_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["browse_depth", "max_depth", "remaining"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // OPC DA namespace hierarchy: 1-20 levels deep
    ctx.push_obligation(ProofObligation::assume("bd", "browse_depth == 7"));
    ctx.push_obligation(ProofObligation::assume("md", "max_depth == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "rm_def",
        "remaining == max_depth - browse_depth",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if browse_depth >= 1 && browse_depth <= max_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_13", "remaining == 13"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OPC DA: browse_depth=7, 13 remaining of 20");
}

#[test]
fn timestamp_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["timestamp_resolution", "samples_per_sec", "max_resolution"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // Timestamp resolution in μs, bounded 1-1000000. samples_per_sec = 1000000 / resolution
    ctx.push_obligation(ProofObligation::assume("tr", "timestamp_resolution == 100")); // 100μs
    ctx.push_obligation(ProofObligation::assume("mr", "max_resolution == 1000000"));
    ctx.push_obligation(ProofObligation::assume(
        "sp_def",
        "samples_per_sec == 1000000 / timestamp_resolution",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if timestamp_resolution >= 1 && timestamp_resolution <= max_resolution { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_10000",
        "samples_per_sec == 10000",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "OPC DA: 100μs resolution → 10000 samples/sec");
}
