// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn objects_per_slab() {
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
    expect_verified_or_unknown(&result, "slab: 4096 / 64 = 64 objects per slab");
}

#[test]
fn free_list_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &["free_count_before", "free_count_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fcb", "free_count_before == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "fca_def",
        "free_count_after == free_count_before - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_29", "free_count_after == 29"));
    ctx.push_obligation(ProofObligation::assert(
        "decreased",
        "free_count_after < free_count_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "slab alloc: free 30 → 29");
}

#[test]
fn free_list_deallocation() {
    let mut ctx = VerificationContext::new();
    for v in &["free_count_before", "free_count_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("fcb", "free_count_before == 29"));
    ctx.push_obligation(ProofObligation::assume(
        "fca_def",
        "free_count_after == free_count_before + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_30", "free_count_after == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "increased",
        "free_count_after > free_count_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "slab free: free 29 → 30");
}

#[test]
fn slab_states() {
    // Slab states: full (0 free), partial (some free), empty (all free)
    let mut ctx = VerificationContext::new();
    for v in &["total_objects", "free_objects"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("state", i32_ty()); // 0=full, 1=partial, 2=empty
    ctx.push_obligation(ProofObligation::assume("to", "total_objects == 64"));
    ctx.push_obligation(ProofObligation::assume("fo", "free_objects == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "state == if free_objects == 0 { 0 } else { if free_objects == total_objects { 2 } else { 1 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("partial", "state == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "slab state: 20/64 free → partial");
}

#[test]
fn zero_fragmentation() {
    // Slab allocator: all objects same size → no internal fragmentation
    let mut ctx = VerificationContext::new();
    for v in &["requested", "allocated", "wasted"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "requested == 64"));
    ctx.push_obligation(ProofObligation::assume("a", "allocated == 64")); // exact fit
    ctx.push_obligation(ProofObligation::assume(
        "w_def",
        "wasted == allocated - requested",
    ));
    ctx.push_obligation(ProofObligation::assert("zero", "wasted == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "slab: 64 requested, 64 allocated, 0 waste");
}

#[test]
fn cache_coloring_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["cache_line_size", "slab_index", "color_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cls", "cache_line_size == 64"));
    ctx.push_obligation(ProofObligation::assume("si", "slab_index == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "color_offset == slab_index * cache_line_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_192", "color_offset == 192"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "cache coloring: 3 × 64 = 192 byte offset");
}

#[test]
fn total_memory_in_cache() {
    let mut ctx = VerificationContext::new();
    for v in &["slab_count", "slab_size", "total_memory"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sc", "slab_count == 10"));
    ctx.push_obligation(ProofObligation::assume("ss", "slab_size == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "tm_def",
        "total_memory == slab_count * slab_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40960", "total_memory == 40960"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "slab cache: 10 × 4096 = 40960 bytes");
}

#[test]
fn magazine_layer_batch() {
    let mut ctx = VerificationContext::new();
    for v in &["magazine_size", "allocs_before_refill"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ms", "magazine_size == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "abr_def",
        "allocs_before_refill == magazine_size",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_32",
        "allocs_before_refill == 32",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "positive",
        "allocs_before_refill > 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "magazine: 32 allocs before slab refill");
}

#[test]
fn slab_reaping() {
    let mut ctx = VerificationContext::new();
    for v in &["empty_slabs", "reap_threshold", "slabs_to_free"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("es", "empty_slabs == 8"));
    ctx.push_obligation(ProofObligation::assume("rt", "reap_threshold == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "stf_def",
        "slabs_to_free == empty_slabs - reap_threshold",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "slabs_to_free == 5"));
    ctx.push_obligation(ProofObligation::assert("positive", "slabs_to_free > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reap: 8 empty - 3 threshold = 5 to free");
}

#[test]
fn object_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["object_size", "alignment", "aligned_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Round up to alignment boundary
    ctx.push_obligation(ProofObligation::assume("os", "object_size == 50"));
    ctx.push_obligation(ProofObligation::assume("a", "alignment == 8"));
    // aligned_size = ((object_size + alignment - 1) / alignment) * alignment
    // = (50 + 7) / 8 * 8 = 57/8 * 8 = 7 * 8 = 56
    ctx.push_obligation(ProofObligation::assume(
        "as_def",
        "aligned_size == ((object_size + alignment - 1) / alignment) * alignment",
    ));
    ctx.push_obligation(ProofObligation::assert("is_56", "aligned_size == 56"));
    ctx.push_obligation(ProofObligation::assert("ge", "aligned_size >= object_size"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "alignment: (50+7)/8*8 = 56");
}
