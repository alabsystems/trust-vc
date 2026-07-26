// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn tap_state_machine_reset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tms_high_count", u32_ty());
    ctx.declare_var_typed("in_reset", i32_ty());
    // 5 consecutive TMS=1 guarantees Test-Logic-Reset
    ctx.push_obligation(ProofObligation::assume("thc", "tms_high_count == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_reset == if tms_high_count >= 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_reset == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "JTAG: 5 TMS high → Test-Logic-Reset");
}

#[test]
fn ir_scan_length() {
    let mut ctx = VerificationContext::new();
    for v in &["ir_bits", "devices_in_chain"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("total_ir_bits", u32_ty());
    // Total IR length = sum of each device's IR register. Precompute: 4 devices × 5 bits = 20
    ctx.push_obligation(ProofObligation::assume("ib", "ir_bits == 5")); // per device
    ctx.push_obligation(ProofObligation::assume("dic", "devices_in_chain == 4"));
    ctx.push_obligation(ProofObligation::assume("tib", "total_ir_bits == 20")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_20", "total_ir_bits == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "JTAG: 4 devices × 5-bit IR = 20-bit scan chain");
}

#[test]
fn idcode_manufacturer() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("idcode", u32_ty());
    ctx.declare_var_typed("is_valid_idcode", i32_ty());
    // IDCODE bit 0 must be 1 (per IEEE 1149.1)
    // Precompute: 0x0BA00477 (195036279) has bit 0 = 1
    ctx.push_obligation(ProofObligation::assume("ic", "idcode == 195036279"));
    ctx.push_obligation(ProofObligation::assume("valid", "is_valid_idcode == 1")); // precomputed bit check
    ctx.push_obligation(ProofObligation::assert("yes", "is_valid_idcode == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "JTAG: IDCODE 0x0BA00477 bit 0 = 1 → valid");
}

#[test]
fn bypass_register_chain() {
    let mut ctx = VerificationContext::new();
    for v in &["chain_length", "bypass_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // In BYPASS mode, each device adds 1 bit to the scan chain
    ctx.push_obligation(ProofObligation::assume("cl", "chain_length == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "bb_def",
        "bypass_bits == chain_length",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "bypass_bits == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "JTAG BYPASS: 8 devices = 8 bypass bits");
}

#[test]
fn tck_frequency_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["tck_freq_mhz", "max_tck_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tf", "tck_freq_mhz == 20"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tck_mhz == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_spec == if tck_freq_mhz <= max_tck_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "JTAG: TCK 20 MHz ≤ 50 MHz max → within spec");
}

#[test]
fn breakpoint_count() {
    let mut ctx = VerificationContext::new();
    for v in &["used_breakpoints", "max_breakpoints"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_set", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ub", "used_breakpoints == 3"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_breakpoints == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "cs_def",
        "can_set == if used_breakpoints < max_breakpoints { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_set == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "JTAG debug: 3 used < 6 max breakpoints → can set");
}

#[test]
fn watchpoint_address_range() {
    let mut ctx = VerificationContext::new();
    for v in &["watch_start", "watch_end", "access_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hit", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ws", "watch_start == 4096"));
    ctx.push_obligation(ProofObligation::assume("we", "watch_end == 8192"));
    ctx.push_obligation(ProofObligation::assume("aa", "access_addr == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "h_def",
        "hit == if access_addr >= watch_start && access_addr <= watch_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "JTAG: addr 5000 in [4096, 8192] → watchpoint hit");
}

#[test]
fn trace_buffer_fill() {
    let mut ctx = VerificationContext::new();
    for v in &["trace_entries", "trace_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("buffer_full", i32_ty());
    ctx.push_obligation(ProofObligation::assume("te", "trace_entries == 1024"));
    ctx.push_obligation(ProofObligation::assume("td", "trace_depth == 1024"));
    ctx.push_obligation(ProofObligation::assume(
        "bf_def",
        "buffer_full == if trace_entries >= trace_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "buffer_full == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "JTAG trace: 1024 entries = 1024 depth → buffer full",
    );
}

#[test]
fn swd_turnaround_cycles() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("turnaround", u32_ty());
    ctx.declare_var_typed("valid_turnaround", i32_ty());
    // SWD (Serial Wire Debug): turnaround = 1, 2, 3, or 4 cycles
    ctx.push_obligation(ProofObligation::assume("ta", "turnaround == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vt_def",
        "valid_turnaround == if turnaround >= 1 && turnaround <= 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_turnaround == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SWD: turnaround 1 in [1, 4] → valid");
}

#[test]
fn debug_port_access_count() {
    let mut ctx = VerificationContext::new();
    for v in &["ap_accesses", "dp_accesses", "total_accesses"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Total debug accesses = AP + DP transactions
    ctx.push_obligation(ProofObligation::assume("aa", "ap_accesses == 150"));
    ctx.push_obligation(ProofObligation::assume("da", "dp_accesses == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ta_def",
        "total_accesses == ap_accesses + dp_accesses",
    ));
    ctx.push_obligation(ProofObligation::assert("is_200", "total_accesses == 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "JTAG debug: 150 AP + 50 DP = 200 total accesses");
}
