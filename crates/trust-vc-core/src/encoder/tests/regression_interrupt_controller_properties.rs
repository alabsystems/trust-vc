// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn highest_priority_wins() {
    let mut ctx = VerificationContext::new();
    for v in &["irq_a_priority", "irq_b_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("a_serviced_first", i32_ty());
    // Lower number = higher priority (ARM GIC convention)
    ctx.push_obligation(ProofObligation::assume("ap", "irq_a_priority == 2"));
    ctx.push_obligation(ProofObligation::assume("bp", "irq_b_priority == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "asf_def",
        "a_serviced_first == if irq_a_priority < irq_b_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "a_serviced_first == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "INTC: IRQ A(2) < IRQ B(10) → A first");
}

#[test]
fn pending_register_set() {
    let mut ctx = VerificationContext::new();
    for v in &["old_pending", "irq_bit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("new_pending", u32_ty());
    ctx.push_obligation(ProofObligation::assume("op", "old_pending == 0"));
    ctx.push_obligation(ProofObligation::assume("ib", "irq_bit == 8")); // IRQ 3 sets bit 3 = 8
    ctx.push_obligation(ProofObligation::assume(
        "np_def",
        "new_pending == old_pending | irq_bit",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "new_pending == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "INTC pending: 0 | 8 = 8");
}

#[test]
fn mask_disables_irq() {
    let mut ctx = VerificationContext::new();
    for v in &["pending", "mask"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("effective", u32_ty());
    ctx.declare_var_typed("irq_active", i32_ty());
    // pending=0xFF (all pending), mask=0x00 (all masked)
    ctx.push_obligation(ProofObligation::assume("p", "pending == 255"));
    ctx.push_obligation(ProofObligation::assume("m", "mask == 0")); // all masked
    ctx.push_obligation(ProofObligation::assume(
        "e_def",
        "effective == pending & mask",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "irq_active == if effective > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("none", "irq_active == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "INTC mask: 255 & 0 = 0 → no active IRQs");
}

#[test]
fn nested_interrupt_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["current_priority", "incoming_priority"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("preempt", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cp", "current_priority == 5"));
    ctx.push_obligation(ProofObligation::assume("ip", "incoming_priority == 2")); // higher priority
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "preempt == if incoming_priority < current_priority { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "preempt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nested IRQ: priority 2 < 5 → preempt");
}

#[test]
fn eoi_clears_active() {
    let mut ctx = VerificationContext::new();
    for v in &["active_before", "irq_bit", "active_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // EOI clears the bit: active_after = active_before & ~irq_bit
    // active=0xFF, clear bit 3 (0x08): 0xFF & ~0x08 = 0xFF & 0xF7 = 0xF7 = 247
    ctx.push_obligation(ProofObligation::assume("ab", "active_before == 255"));
    ctx.push_obligation(ProofObligation::assume("ib", "irq_bit == 8"));
    ctx.push_obligation(ProofObligation::assume("aa", "active_after == 247")); // 255 & ~8 = 247
    ctx.push_obligation(ProofObligation::assert("is_247", "active_after == 247"));
    ctx.push_obligation(ProofObligation::assert(
        "cleared",
        "active_after < active_before",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EOI: active 255 → 247 (bit 3 cleared)");
}

#[test]
fn interrupt_latency() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "detection_cycles",
        "priority_cycles",
        "context_save_cycles",
        "total_latency",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("dc", "detection_cycles == 1"));
    ctx.push_obligation(ProofObligation::assume("pc", "priority_cycles == 3"));
    ctx.push_obligation(ProofObligation::assume("csc", "context_save_cycles == 12"));
    ctx.push_obligation(ProofObligation::assume(
        "tl_def",
        "total_latency == detection_cycles + priority_cycles + context_save_cycles",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "total_latency == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IRQ latency: 1+3+12=16 cycles");
}

#[test]
fn vector_table_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["irq_number", "entry_size", "base_addr", "vector_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("in", "irq_number == 32")); // first peripheral IRQ
    ctx.push_obligation(ProofObligation::assume("es", "entry_size == 4"));
    ctx.push_obligation(ProofObligation::assume("ba", "base_addr == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "vector_addr == base_addr + irq_number * entry_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_128", "vector_addr == 128")); // 32*4
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "IVT: IRQ 32 × 4 = offset 128");
}

#[test]
fn group_priority_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["priority_bits", "group_bits", "subpriority_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // ARM GIC: 8 priority bits split into group + subpriority
    ctx.push_obligation(ProofObligation::assume("pb", "priority_bits == 8"));
    ctx.push_obligation(ProofObligation::assume("gb", "group_bits == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "sb_def",
        "subpriority_bits == priority_bits - group_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "subpriority_bits == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "INTC: 8-4=4 subpriority bits");
}

#[test]
fn software_generated_interrupt() {
    let mut ctx = VerificationContext::new();
    for v in &["sgi_id", "max_sgi"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // SGIs: IDs 0-15
    ctx.push_obligation(ProofObligation::assume("si", "sgi_id == 12"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_sgi == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if sgi_id <= max_sgi { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SGI: ID 12 <= 15 → valid");
}

#[test]
fn distributor_target_cpu() {
    let mut ctx = VerificationContext::new();
    for v in &["target_mask", "num_cpus"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("targets_cpu0", i32_ty());
    // CPU target mask: bit 0 = CPU0, bit 1 = CPU1, etc.
    ctx.push_obligation(ProofObligation::assume("tm", "target_mask == 5")); // CPU0 + CPU2
    ctx.push_obligation(ProofObligation::assume("nc", "num_cpus == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "tc0_def",
        "targets_cpu0 == if target_mask & 1 == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "targets_cpu0 == 1")); // bit 0 set in 5 (101b)
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "INTC dist: mask 5 (101b) targets CPU0");
}
