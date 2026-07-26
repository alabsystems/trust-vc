// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn shared_memory_region_size() {
    let mut ctx = VerificationContext::new();
    for v in &["page_size", "num_pages", "region_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Shared memory region = pages × page_size
    ctx.push_obligation(ProofObligation::assume("ps", "page_size == 4096"));
    ctx.push_obligation(ProofObligation::assume("np", "num_pages == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "rb_def",
        "region_bytes == page_size * num_pages",
    ));
    ctx.push_obligation(ProofObligation::assert("is_65536", "region_bytes == 65536"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "IPC shm: 4096 × 16 = 65536 bytes");
}

#[test]
fn pipe_buffer_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["pipe_pages", "page_size", "pipe_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("above_minimum", i32_ty());
    // Default Linux pipe = 16 pages × 4096 = 65536 bytes
    ctx.push_obligation(ProofObligation::assume("pp", "pipe_pages == 16"));
    ctx.push_obligation(ProofObligation::assume("ps", "page_size == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "pc_def",
        "pipe_capacity == pipe_pages * page_size",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "am_def",
        "above_minimum == if pipe_capacity >= 4096 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_65536",
        "pipe_capacity == 65536",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "above_minimum == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "IPC pipe: 16 × 4096 = 65536 byte buffer");
}

#[test]
fn message_queue_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["current_msgs", "max_msgs"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_enqueue", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cm", "current_msgs == 7"));
    ctx.push_obligation(ProofObligation::assume("mm", "max_msgs == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ce_def",
        "can_enqueue == if current_msgs < max_msgs { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_enqueue == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IPC mq: 7 < 10 max → can enqueue");
}

#[test]
fn semaphore_wait_count() {
    let mut ctx = VerificationContext::new();
    for v in &["sem_value", "waiters"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("should_block", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sv", "sem_value == 0"));
    ctx.push_obligation(ProofObligation::assume("w", "waiters == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "sb_def",
        "should_block == if sem_value == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "should_block == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IPC sem: value=0 → block");
}

#[test]
fn signal_pending_mask() {
    let mut ctx = VerificationContext::new();
    for v in &["pending_signals", "blocked_mask", "deliverable"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_deliverable", i32_ty());
    // Deliverable = pending AND NOT blocked
    // pending=0x0F (signals 0-3), blocked=0x03 (signals 0-1)
    // deliverable = 0x0F & ~0x03 = 0x0F & 0xFC = 0x0C
    ctx.push_obligation(ProofObligation::assume("ps", "pending_signals == 15")); // 0x0F
    ctx.push_obligation(ProofObligation::assume("bm", "blocked_mask == 3")); // 0x03
    ctx.push_obligation(ProofObligation::assume("d", "deliverable == 12")); // precomputed 0x0C
    ctx.push_obligation(ProofObligation::assume(
        "hd_def",
        "has_deliverable == if deliverable > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_12", "deliverable == 12"));
    ctx.push_obligation(ProofObligation::assert("yes", "has_deliverable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "IPC signal: pending=0x0F, blocked=0x03 → deliverable=0x0C",
    );
}

#[test]
fn unix_socket_backlog() {
    let mut ctx = VerificationContext::new();
    for v in &["pending_connections", "backlog_limit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("accept_new", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pc", "pending_connections == 50"));
    ctx.push_obligation(ProofObligation::assume("bl", "backlog_limit == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "an_def",
        "accept_new == if pending_connections < backlog_limit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "accept_new == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IPC socket: 50 pending < 128 backlog → accept");
}

#[test]
fn futex_wake_count() {
    let mut ctx = VerificationContext::new();
    for v in &["waiters", "wake_count", "remaining_waiters"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Wake up to wake_count waiters
    ctx.push_obligation(ProofObligation::assume("w", "waiters == 10"));
    ctx.push_obligation(ProofObligation::assume("wc", "wake_count == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "rw_def",
        "remaining_waiters == if waiters > wake_count { waiters - wake_count } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_7", "remaining_waiters == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IPC futex: 10 waiters - wake 3 = 7 remaining");
}

#[test]
fn eventfd_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["current_value", "write_value", "new_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("would_overflow", i32_ty());
    // eventfd counter increments on write
    ctx.push_obligation(ProofObligation::assume("cv", "current_value == 100"));
    ctx.push_obligation(ProofObligation::assume("wv", "write_value == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "nv_def",
        "new_value == current_value + write_value",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "would_overflow == if new_value < current_value { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_150", "new_value == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "no_overflow",
        "would_overflow == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IPC eventfd: 100 + 50 = 150 (no overflow)");
}

#[test]
fn mmap_offset_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["file_offset", "page_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    // mmap offset must be page-aligned
    ctx.push_obligation(ProofObligation::assume("fo", "file_offset == 8192")); // 2 pages
    ctx.push_obligation(ProofObligation::assume("ps", "page_size == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "aligned == if file_offset % page_size == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "IPC mmap: 8192 % 4096 == 0 → aligned");
}

#[test]
fn dbus_message_header_size() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "fixed_header",
        "field_count",
        "field_size",
        "header_padding",
        "total_header",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // D-Bus header: 12 bytes fixed + field array + padding to 8-byte boundary
    // Precompute: 12 + 20 + 0 = 32 (already aligned)
    ctx.push_obligation(ProofObligation::assume("fh", "fixed_header == 12"));
    ctx.push_obligation(ProofObligation::assume("fc", "field_count == 4"));
    ctx.push_obligation(ProofObligation::assume("fs", "field_size == 20")); // precomputed
    ctx.push_obligation(ProofObligation::assume("hp", "header_padding == 0")); // 32 is 8-aligned
    ctx.push_obligation(ProofObligation::assume(
        "th_def",
        "total_header == fixed_header + field_size + header_padding",
    ));
    ctx.push_obligation(ProofObligation::assert("is_32", "total_header == 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IPC D-Bus: 12 + 20 + 0 = 32-byte header");
}
