// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn page_erase_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "page_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "address == 8192")); // 0x2000
    ctx.push_obligation(ProofObligation::assume("ps", "page_size == 2048"));
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "aligned == if address % page_size == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "flash: 8192 mod 2048 = 0 → aligned");
}

#[test]
fn sector_contains_address() {
    let mut ctx = VerificationContext::new();
    for v in &["sector_start", "sector_size", "address"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_sector", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ss", "sector_start == 65536")); // 64KB
    ctx.push_obligation(ProofObligation::assume("sz", "sector_size == 65536"));
    ctx.push_obligation(ProofObligation::assume("a", "address == 80000"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "in_sector == if address >= sector_start && address < sector_start + sector_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_sector == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flash: 80000 in [65536, 131072)");
}

#[test]
fn write_granularity() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bytes", "write_unit", "writes_needed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Flash writes in units (e.g., 4 bytes for STM32)
    ctx.push_obligation(ProofObligation::assume("db", "data_bytes == 256"));
    ctx.push_obligation(ProofObligation::assume("wu", "write_unit == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "wn_def",
        "writes_needed == data_bytes / write_unit",
    ));
    ctx.push_obligation(ProofObligation::assert("is_64", "writes_needed == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "flash: 256/4=64 write operations");
}

#[test]
fn wait_states_for_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["hclk_mhz", "wait_states"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // STM32F1: 0 WS for ≤24MHz, 1 WS for ≤48MHz, 2 WS for ≤72MHz
    ctx.push_obligation(ProofObligation::assume("hc", "hclk_mhz == 72"));
    ctx.push_obligation(ProofObligation::assume("ws", "wait_states == 2"));
    ctx.push_obligation(ProofObligation::assert("is_2", "wait_states == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flash: 72MHz → 2 wait states");
}

#[test]
fn prefetch_buffer_hit() {
    let mut ctx = VerificationContext::new();
    for v in &["total_reads", "cache_hits", "cache_misses"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tr", "total_reads == 1000"));
    ctx.push_obligation(ProofObligation::assume("ch", "cache_hits == 950"));
    ctx.push_obligation(ProofObligation::assume(
        "cm_def",
        "cache_misses == total_reads - cache_hits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "cache_misses == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "mostly_hits",
        "cache_hits > cache_misses",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flash prefetch: 1000-950=50 misses");
}

#[test]
fn erase_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cell_value", u32_ty());
    ctx.declare_var_typed("erased_value", u32_ty());
    ctx.declare_var_typed("erase_ok", i32_ty());
    // Erased flash reads as 0xFF (all 1s)
    ctx.push_obligation(ProofObligation::assume("cv", "cell_value == 255")); // 0xFF
    ctx.push_obligation(ProofObligation::assume("ev", "erased_value == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "erase_ok == if cell_value == erased_value { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "erase_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flash erase: cell=0xFF → verified erased");
}

#[test]
fn write_protection_region() {
    let mut ctx = VerificationContext::new();
    for v in &["write_addr", "protect_start", "protect_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("protected", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wa", "write_addr == 16384"));
    ctx.push_obligation(ProofObligation::assume("ps", "protect_start == 0"));
    ctx.push_obligation(ProofObligation::assume("pe", "protect_end == 32768"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "protected == if write_addr >= protect_start && write_addr < protect_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "protected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flash WP: 16384 in [0, 32768) → protected");
}

#[test]
fn dual_bank_selection() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "bank_boundary"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bank", i32_ty()); // 0=bank1, 1=bank2
    ctx.push_obligation(ProofObligation::assume("a", "address == 524288")); // 512KB
    ctx.push_obligation(ProofObligation::assume("bb", "bank_boundary == 262144")); // 256KB
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "bank == if address >= bank_boundary { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("bank2", "bank == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flash: 524288 >= 262144 → bank 2");
}

#[test]
fn program_cycle_count() {
    let mut ctx = VerificationContext::new();
    for v in &["old_cycles", "new_cycles", "max_cycles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_life", i32_ty());
    ctx.push_obligation(ProofObligation::assume("oc", "old_cycles == 9999"));
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_cycles == old_cycles + 1",
    ));
    ctx.push_obligation(ProofObligation::assume("mc", "max_cycles == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "wl_def",
        "within_life == if new_cycles <= max_cycles { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10000", "new_cycles == 10000"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_life == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flash: 10000 <= 100000 endurance cycles");
}

#[test]
fn option_bytes_valid() {
    let mut ctx = VerificationContext::new();
    for v in &["option_byte", "complement"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // Option bytes stored with complement for integrity
    ctx.push_obligation(ProofObligation::assume("ob", "option_byte == 170")); // 0xAA
    ctx.push_obligation(ProofObligation::assume("c", "complement == 85")); // 0x55
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if option_byte + complement == 255 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flash option: 0xAA + 0x55 = 0xFF → valid");
}
