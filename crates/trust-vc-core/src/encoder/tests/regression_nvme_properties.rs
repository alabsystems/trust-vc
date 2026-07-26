// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn submission_queue_tail_advance() {
    let mut ctx = VerificationContext::new();
    for v in &["sq_tail", "sq_size", "new_tail"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Submission queue tail wraps around
    ctx.push_obligation(ProofObligation::assume("st", "sq_tail == 63"));
    ctx.push_obligation(ProofObligation::assume("ss", "sq_size == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "nt_def",
        "new_tail == (sq_tail + 1) % sq_size",
    ));
    ctx.push_obligation(ProofObligation::assert("wraps", "new_tail == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "NVMe SQ: tail 63 + 1 mod 64 = 0");
}

#[test]
fn completion_queue_phase_tag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase_bit", u32_ty());
    ctx.declare_var_typed("entry_phase", u32_ty());
    ctx.declare_var_typed("is_new_completion", i32_ty());
    // Phase tag: new completions have phase matching current expected phase
    ctx.push_obligation(ProofObligation::assume("pb", "phase_bit == 1"));
    ctx.push_obligation(ProofObligation::assume("ep", "entry_phase == 1")); // matches
    ctx.push_obligation(ProofObligation::assume(
        "inc_def",
        "is_new_completion == if entry_phase == phase_bit { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_new_completion == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NVMe CQ: phase 1 matches → new completion");
}

#[test]
fn queue_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["sq_entries", "cq_entries", "max_entries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_depth", i32_ty());
    // NVMe: max queue depth 65536 entries, CQ must be >= SQ
    ctx.push_obligation(ProofObligation::assume("sqe", "sq_entries == 1024"));
    ctx.push_obligation(ProofObligation::assume("cqe", "cq_entries == 1024"));
    ctx.push_obligation(ProofObligation::assume("me", "max_entries == 65536"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_depth == if sq_entries <= max_entries && cq_entries >= sq_entries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_depth == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NVMe: SQ=1024, CQ=1024 within limits");
}

#[test]
fn namespace_lba_count() {
    let mut ctx = VerificationContext::new();
    for v in &["total_blocks", "block_size_bytes", "capacity_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 1M blocks × 4096 bytes = 4GB
    // Precompute since full product overflows u32; use a smaller example
    // 256K blocks × 4096 = 1GB (fits in u32)
    ctx.push_obligation(ProofObligation::assume("tb", "total_blocks == 262144")); // 256K
    ctx.push_obligation(ProofObligation::assume("bs", "block_size_bytes == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "cb_def",
        "capacity_bytes == total_blocks * block_size_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_1gb",
        "capacity_bytes == 1073741824",
    )); // 1GB
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "NVMe: 256K × 4096 = 1GB");
}

#[test]
fn io_command_opcode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opcode", u32_ty());
    ctx.declare_var_typed("is_read", i32_ty());
    ctx.declare_var_typed("is_write", i32_ty());
    // NVMe I/O opcodes: Read=0x02, Write=0x01
    ctx.push_obligation(ProofObligation::assume("op", "opcode == 2")); // Read
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_read == if opcode == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "iw_def",
        "is_write == if opcode == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("read_yes", "is_read == 1"));
    ctx.push_obligation(ProofObligation::assert("write_no", "is_write == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NVMe: opcode 2 → Read, not Write");
}

#[test]
fn prp_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["prp_address", "page_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    // PRP (Physical Region Page) must be page-aligned
    ctx.push_obligation(ProofObligation::assume("pa", "prp_address == 8388608")); // 8MB
    ctx.push_obligation(ProofObligation::assume("ps", "page_size == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "aligned == if prp_address % page_size == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "NVMe PRP: 8MB page-aligned to 4KB");
}

#[test]
fn admin_queue_doorbell() {
    let mut ctx = VerificationContext::new();
    for v in &["old_tail", "commands_added", "queue_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("new_doorbell", u32_ty());
    // Writing doorbell advances tail pointer
    ctx.push_obligation(ProofObligation::assume("ot", "old_tail == 5"));
    ctx.push_obligation(ProofObligation::assume("ca", "commands_added == 3"));
    ctx.push_obligation(ProofObligation::assume("qs", "queue_size == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "nd_def",
        "new_doorbell == (old_tail + commands_added) % queue_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "new_doorbell == 8")); // 5+3 mod 32 = 8
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "NVMe doorbell: (5+3) mod 32 = 8");
}

#[test]
fn interrupt_coalescing() {
    let mut ctx = VerificationContext::new();
    for v in &["completions_pending", "coalesce_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fire_interrupt", i32_ty());
    // Coalesce: only fire interrupt when threshold completions accumulate
    ctx.push_obligation(ProofObligation::assume("cp", "completions_pending == 8"));
    ctx.push_obligation(ProofObligation::assume("ct", "coalesce_threshold == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "fi_def",
        "fire_interrupt == if completions_pending >= coalesce_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fire_interrupt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NVMe: 8 >= 4 threshold → fire interrupt");
}

#[test]
fn controller_status_ready() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("csts_rdy", u32_ty());
    ctx.declare_var_typed("cc_en", u32_ty());
    ctx.declare_var_typed("operational", i32_ty());
    // Controller operational when CC.EN=1 and CSTS.RDY=1
    ctx.push_obligation(ProofObligation::assume("cr", "csts_rdy == 1"));
    ctx.push_obligation(ProofObligation::assume("ce", "cc_en == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "op_def",
        "operational == if csts_rdy == 1 && cc_en == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "operational == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NVMe: CC.EN=1, CSTS.RDY=1 → operational");
}

#[test]
fn outstanding_commands_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["issued", "completed", "outstanding", "max_outstanding"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_issue", i32_ty());
    ctx.push_obligation(ProofObligation::assume("i", "issued == 500"));
    ctx.push_obligation(ProofObligation::assume("c", "completed == 450"));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "outstanding == issued - completed",
    ));
    ctx.push_obligation(ProofObligation::assume("mo", "max_outstanding == 1024"));
    ctx.push_obligation(ProofObligation::assume(
        "ci_def",
        "can_issue == if outstanding < max_outstanding { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "outstanding == 50"));
    ctx.push_obligation(ProofObligation::assert("yes", "can_issue == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NVMe: 500-450=50 outstanding < 1024 → can issue");
}
