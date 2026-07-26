// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pool_allocate_from_free() {
    let mut ctx = VerificationContext::new();
    for v in &["free_count", "alloc_count", "new_free", "new_alloc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("free_val", "free_count == 10"));
    ctx.push_obligation(ProofObligation::assume("alloc_val", "alloc_count == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "new_free_def",
        "new_free == free_count - 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "new_alloc_def",
        "new_alloc == alloc_count + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("free_dec", "new_free == 9"));
    ctx.push_obligation(ProofObligation::assert("alloc_inc", "new_alloc == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "allocate: free--, alloc++");
}

#[test]
fn pool_total_conserved() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "free",
        "alloc",
        "total",
        "new_free",
        "new_alloc",
        "new_total",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("free_val", "free == 8"));
    ctx.push_obligation(ProofObligation::assume("alloc_val", "alloc == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "total_def",
        "total == free + alloc",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "new_free_def",
        "new_free == free - 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "new_alloc_def",
        "new_alloc == alloc + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "new_total_def",
        "new_total == new_free + new_alloc",
    ));
    ctx.push_obligation(ProofObligation::assert("conserved", "new_total == total"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pool total conserved after alloc");
}

#[test]
fn pool_release_returns_to_free() {
    let mut ctx = VerificationContext::new();
    for v in &["free", "alloc", "new_free", "new_alloc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("free_val", "free == 3"));
    ctx.push_obligation(ProofObligation::assume("alloc_val", "alloc == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "new_free_def",
        "new_free == free + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "new_alloc_def",
        "new_alloc == alloc - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("free_inc", "new_free == 4"));
    ctx.push_obligation(ProofObligation::assert("alloc_dec", "new_alloc == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "release: free++, alloc--");
}

#[test]
fn pool_empty_no_alloc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("free", u32_ty());
    ctx.declare_var_typed("can_alloc", i32_ty());
    ctx.push_obligation(ProofObligation::assume("free_val", "free == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "can_alloc_def",
        "can_alloc == if free > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("blocked", "can_alloc == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "empty pool blocks allocation");
}

#[test]
fn slab_index_within_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["slab_size", "index", "base", "addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("slab", "slab_size == 64"));
    ctx.push_obligation(ProofObligation::assume("idx", "index == 3"));
    ctx.push_obligation(ProofObligation::assume("base_val", "base == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "addr_def",
        "addr == base + index * slab_size",
    ));
    ctx.push_obligation(ProofObligation::assert("in_range", "addr >= base"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "slab address >= base");
}

#[test]
fn pool_high_watermark() {
    let mut ctx = VerificationContext::new();
    for v in &["alloc", "watermark", "new_alloc", "new_watermark"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("alloc_val", "alloc == 5"));
    ctx.push_obligation(ProofObligation::assume("wm_val", "watermark == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "new_alloc_def",
        "new_alloc == alloc + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "new_wm_def",
        "new_watermark == if new_alloc > watermark { new_alloc } else { watermark }",
    ));
    // 6 <= 7, so watermark stays
    ctx.push_obligation(ProofObligation::assert(
        "wm_unchanged",
        "new_watermark == 7",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "watermark stays when alloc < watermark");
}

#[test]
fn pool_watermark_updates() {
    let mut ctx = VerificationContext::new();
    for v in &["alloc", "watermark", "new_alloc", "new_watermark"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("alloc_val", "alloc == 7"));
    ctx.push_obligation(ProofObligation::assume("wm_val", "watermark == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "new_alloc_def",
        "new_alloc == alloc + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "new_wm_def",
        "new_watermark == if new_alloc > watermark { new_alloc } else { watermark }",
    ));
    // 8 > 7, so watermark updates
    ctx.push_obligation(ProofObligation::assert("wm_updated", "new_watermark == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "watermark updates when new alloc exceeds it");
}

#[test]
fn pool_batch_allocate() {
    let mut ctx = VerificationContext::new();
    for v in &["free", "batch", "new_free"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("free_val", "free == 20"));
    ctx.push_obligation(ProofObligation::assume("batch_val", "batch == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "new_free_def",
        "new_free == free - batch",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "new_free == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "batch allocate 5 from 20 free = 15");
}

#[test]
fn pool_utilization_ratio() {
    // utilization = alloc / total (compare with threshold)
    let mut ctx = VerificationContext::new();
    for v in &["alloc", "total", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("over_threshold", i32_ty());
    ctx.push_obligation(ProofObligation::assume("alloc_val", "alloc == 8"));
    ctx.push_obligation(ProofObligation::assume("total_val", "total == 10"));
    // 80% threshold: alloc * 100 >= total * 80
    ctx.push_obligation(ProofObligation::assume("threshold_val", "threshold == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "over_def",
        "over_threshold == if alloc * 100 >= total * threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_over", "over_threshold == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "8/10 = 80% >= 80% threshold");
}

#[test]
fn pool_alloc_release_cycle() {
    let mut ctx = VerificationContext::new();
    for v in &["free", "after_alloc", "after_release"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("free_val", "free == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "after_alloc_def",
        "after_alloc == free - 3",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "after_release_def",
        "after_release == after_alloc + 3",
    ));
    ctx.push_obligation(ProofObligation::assert("restored", "after_release == free"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "alloc 3 then release 3 = original free count");
}
