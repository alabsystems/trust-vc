// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn store_buffer_drain() {
    let mut ctx = VerificationContext::new();
    for v in &["entries_before", "entries_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Store fence drains all buffered stores
    ctx.push_obligation(ProofObligation::assume("eb", "entries_before == 8"));
    ctx.push_obligation(ProofObligation::assume("ea", "entries_after == 0")); // all drained
    ctx.push_obligation(ProofObligation::assert("empty", "entries_after == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "flushed",
        "entries_after < entries_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "store fence: 8 entries → 0 (drained)");
}

#[test]
fn acquire_semantics() {
    // Acquire: no loads/stores after can be reordered before
    let mut ctx = VerificationContext::new();
    for v in &["acquire_seq", "load_after_seq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ordered", i32_ty());
    ctx.push_obligation(ProofObligation::assume("as", "acquire_seq == 100"));
    ctx.push_obligation(ProofObligation::assume("las", "load_after_seq == 101"));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "ordered == if load_after_seq > acquire_seq { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "ordered == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "acquire: load_after(101) > acquire(100)");
}

#[test]
fn release_semantics() {
    // Release: no loads/stores before can be reordered after
    let mut ctx = VerificationContext::new();
    for v in &["store_before_seq", "release_seq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ordered", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sbs", "store_before_seq == 99"));
    ctx.push_obligation(ProofObligation::assume("rs", "release_seq == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "ordered == if store_before_seq < release_seq { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "ordered == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "release: store_before(99) < release(100)");
}

#[test]
fn seq_cst_total_order() {
    // SeqCst: all operations appear in a single total order
    let mut ctx = VerificationContext::new();
    for v in &["op_a_seq", "op_b_seq", "op_c_seq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("total_order", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "op_a_seq == 1"));
    ctx.push_obligation(ProofObligation::assume("b", "op_b_seq == 2"));
    ctx.push_obligation(ProofObligation::assume("c", "op_c_seq == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "total_order == if op_a_seq < op_b_seq && op_b_seq < op_c_seq { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "total_order == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SeqCst: 1 < 2 < 3 total order");
}

#[test]
fn load_buffer_entries() {
    let mut ctx = VerificationContext::new();
    for v in &["pending_loads", "max_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_capacity", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pl", "pending_loads == 12"));
    ctx.push_obligation(ProofObligation::assume("me", "max_entries == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "hc_def",
        "has_capacity == if pending_loads < max_entries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "has_capacity == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "load buffer: 12/32 → has capacity");
}

#[test]
fn write_combining_buffer() {
    let mut ctx = VerificationContext::new();
    for v in &["writes_combined", "cache_line_bytes", "bytes_written"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Write combining: accumulate writes until full cache line
    ctx.push_obligation(ProofObligation::assume("wc", "writes_combined == 8")); // 8 writes of 8 bytes
    ctx.push_obligation(ProofObligation::assume("cl", "cache_line_bytes == 64"));
    ctx.push_obligation(ProofObligation::assume("bw", "bytes_written == 64")); // full line
    ctx.push_obligation(ProofObligation::assert(
        "full_line",
        "bytes_written == cache_line_bytes",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "write combining: 64 bytes = full cache line");
}

#[test]
fn fence_instruction_cost() {
    let mut ctx = VerificationContext::new();
    for v in &["cycles_without_fence", "fence_penalty", "cycles_with_fence"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cwf", "cycles_without_fence == 10"));
    ctx.push_obligation(ProofObligation::assume("fp", "fence_penalty == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "cf_def",
        "cycles_with_fence == cycles_without_fence + fence_penalty",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "cycles_with_fence == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "slower",
        "cycles_with_fence > cycles_without_fence",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fence cost: 10+40=50 cycles");
}

#[test]
fn memory_order_relaxation_level() {
    // 0=Relaxed, 1=Acquire, 2=Release, 3=AcqRel, 4=SeqCst
    let mut ctx = VerificationContext::new();
    for v in &["order_a", "order_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("a_stronger", i32_ty());
    ctx.push_obligation(ProofObligation::assume("oa", "order_a == 4")); // SeqCst
    ctx.push_obligation(ProofObligation::assume("ob", "order_b == 1")); // Acquire
    ctx.push_obligation(ProofObligation::assume(
        "as_def",
        "a_stronger == if order_a > order_b { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "a_stronger == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ordering: SeqCst(4) > Acquire(1)");
}

#[test]
fn data_dependency_ordering() {
    // Data dependency: load B depends on value loaded from A
    let mut ctx = VerificationContext::new();
    for v in &["load_a_seq", "load_b_seq"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dep_ordered", i32_ty());
    ctx.push_obligation(ProofObligation::assume("las", "load_a_seq == 50"));
    ctx.push_obligation(ProofObligation::assume("lbs", "load_b_seq == 51")); // depends on A
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dep_ordered == if load_a_seq < load_b_seq { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "dep_ordered == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "data dep: load_a(50) < load_b(51)");
}

#[test]
fn store_forwarding() {
    let mut ctx = VerificationContext::new();
    for v in &["store_value", "forwarded_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("forwarded", i32_ty());
    // Store forwarding: subsequent load gets value from store buffer
    ctx.push_obligation(ProofObligation::assume("sv", "store_value == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "fv",
        "forwarded_value == store_value",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "forwarded == if forwarded_value == store_value { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("match", "forwarded_value == 42"));
    ctx.push_obligation(ProofObligation::assert("ok", "forwarded == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "store forward: value 42 forwarded");
}
