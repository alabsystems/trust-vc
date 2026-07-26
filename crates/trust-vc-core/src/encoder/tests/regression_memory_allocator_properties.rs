// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn alloc_decreases_free_memory() {
    let mut ctx = VerificationContext::new();
    for v in &["free_before", "alloc_size", "free_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fb", "free_before == 1024"));
    ctx.push_obligation(ProofObligation::assume("as", "alloc_size == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "fa_def",
        "free_after == free_before - alloc_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_768", "free_after == 768"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "alloc: 1024 - 256 = 768 free");
}

#[test]
fn free_increases_free_memory() {
    let mut ctx = VerificationContext::new();
    for v in &["free_before", "freed_size", "free_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fb", "free_before == 768"));
    ctx.push_obligation(ProofObligation::assume("fs", "freed_size == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "fa_def",
        "free_after == free_before + freed_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1024", "free_after == 1024"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "free: 768 + 256 = 1024");
}

#[test]
fn total_memory_invariant() {
    let mut ctx = VerificationContext::new();
    for v in &["used", "free", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("u", "used == 300"));
    ctx.push_obligation(ProofObligation::assume("f", "free == 724"));
    ctx.push_obligation(ProofObligation::assume("t", "total == 1024"));
    ctx.push_obligation(ProofObligation::assert("conserved", "used + free == total"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "memory invariant: 300 + 724 = 1024");
}

#[test]
fn alignment_rounds_up() {
    let mut ctx = VerificationContext::new();
    for v in &["requested", "alignment", "aligned_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "requested == 13"));
    ctx.push_obligation(ProofObligation::assume("a", "alignment == 8"));
    // Round up: ((requested + alignment - 1) / alignment) * alignment
    ctx.push_obligation(ProofObligation::assume(
        "as_def",
        "aligned_size == ((requested + alignment - 1) / alignment) * alignment",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "aligned_size == 16"));
    ctx.push_obligation(ProofObligation::assert(
        "geq_req",
        "aligned_size >= requested",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "align 13 to 8 → 16");
}

#[test]
fn buddy_system_split() {
    // Splitting a block of size 2^k gives two blocks of size 2^(k-1)
    let mut ctx = VerificationContext::new();
    for v in &["parent_size", "child_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "parent_size == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "child_size == parent_size / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_256", "child_size == 256"));
    ctx.push_obligation(ProofObligation::assert(
        "half",
        "child_size + child_size == parent_size",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "buddy split: 512 → 2×256");
}

#[test]
fn coalesce_doubles_block() {
    let mut ctx = VerificationContext::new();
    for v in &["block_a", "block_b", "merged"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "block_a == 256"));
    ctx.push_obligation(ProofObligation::assume("b", "block_b == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "merged == block_a + block_b",
    ));
    ctx.push_obligation(ProofObligation::assert("is_512", "merged == 512"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "coalesce: 256 + 256 = 512");
}

#[test]
fn fragmentation_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["total_free", "largest_free", "fragmentation"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tf", "total_free == 1000"));
    ctx.push_obligation(ProofObligation::assume("lf", "largest_free == 200"));
    // fragmentation = 1 - (largest/total), scaled by 100
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fragmentation == 100 - (largest_free * 100 / total_free)",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "fragmentation == 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "fragmentation: 100 - 200*100/1000 = 80%");
}

#[test]
fn slab_allocation_fixed_size() {
    let mut ctx = VerificationContext::new();
    for v in &["slab_size", "object_size", "objects_per_slab"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ss", "slab_size == 4096"));
    ctx.push_obligation(ProofObligation::assume("os", "object_size == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "ops_def",
        "objects_per_slab == slab_size / object_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_64", "objects_per_slab == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "slab: 4096 / 64 = 64 objects");
}

#[test]
fn watermark_triggers_gc() {
    let mut ctx = VerificationContext::new();
    for v in &["used_memory", "total_memory", "high_watermark"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("trigger_gc", i32_ty());
    ctx.push_obligation(ProofObligation::assume("um", "used_memory == 900"));
    ctx.push_obligation(ProofObligation::assume("tm", "total_memory == 1024"));
    ctx.push_obligation(ProofObligation::assume("hw", "high_watermark == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "tg_def",
        "trigger_gc == if used_memory > high_watermark { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("gc", "trigger_gc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "900 > watermark 800 → trigger GC");
}

#[test]
fn allocation_fails_when_full() {
    let mut ctx = VerificationContext::new();
    for v in &["free_memory", "requested"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_allocate", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fm", "free_memory == 100"));
    ctx.push_obligation(ProofObligation::assume("r", "requested == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "ca_def",
        "can_allocate == if free_memory >= requested { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fails", "can_allocate == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 free < 256 requested → allocation fails");
}
