// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn page_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("page_bytes", u32_ty());
    ctx.declare_var_typed("valid_page", i32_ty());
    // Common NAND page sizes: 2048, 4096, 8192, 16384
    ctx.push_obligation(ProofObligation::assume("pb", "page_bytes == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "vp_def",
        "valid_page == if page_bytes == 2048 || page_bytes == 4096 || page_bytes == 8192 || page_bytes == 16384 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_page == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND controller: 4096B is valid page size");
}

#[test]
fn block_erase_count() {
    let mut ctx = VerificationContext::new();
    for v in &["erase_count", "max_erase_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("life_ok", i32_ty());
    // MLC: ~3000 P/E cycles, TLC: ~1000, SLC: ~100000
    ctx.push_obligation(ProofObligation::assume("ec", "erase_count == 500"));
    ctx.push_obligation(ProofObligation::assume("me", "max_erase_count == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "life_ok == if erase_count < max_erase_count { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "life_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND controller: 500 erases < 3000 max → life OK");
}

#[test]
fn bad_block_count() {
    let mut ctx = VerificationContext::new();
    for v in &["bad_blocks", "max_bad_blocks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bb_ok", i32_ty());
    // Factory + runtime bad blocks must stay below threshold
    ctx.push_obligation(ProofObligation::assume("bb", "bad_blocks == 20"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_bad_blocks == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bb_ok == if bad_blocks <= max_bad_blocks { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bb_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND controller: 20 bad blocks ≤ 80 max → OK");
}

#[test]
fn ecc_correction_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["ecc_bits", "required_ecc_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ecc_ok", i32_ty());
    // ECC strength: BCH or LDPC, e.g., 8-bit/512B, 40-bit/1KB
    ctx.push_obligation(ProofObligation::assume("eb", "ecc_bits == 40"));
    ctx.push_obligation(ProofObligation::assume("re", "required_ecc_bits == 24"));
    ctx.push_obligation(ProofObligation::assume(
        "eo_def",
        "ecc_ok == if ecc_bits >= required_ecc_bits { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ecc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "NAND controller: 40-bit ECC ≥ 24-bit required → OK",
    );
}

#[test]
fn oob_size() {
    let mut ctx = VerificationContext::new();
    for v in &["oob_bytes", "min_oob_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("oob_ok", i32_ty());
    // Out-of-band (spare) area for ECC and metadata
    ctx.push_obligation(ProofObligation::assume("ob", "oob_bytes == 128"));
    ctx.push_obligation(ProofObligation::assume("mo", "min_oob_bytes == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "oob_ok == if oob_bytes >= min_oob_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "oob_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "NAND controller: 128B OOB ≥ 64B min → spare area OK",
    );
}

#[test]
fn pages_per_block() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pages", u32_ty());
    ctx.declare_var_typed("valid_count", i32_ty());
    // Common pages-per-block: 64, 128, 256
    ctx.push_obligation(ProofObligation::assume("p", "pages == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_count == if pages == 64 || pages == 128 || pages == 256 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_count == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND controller: 128 pages/block is valid");
}

#[test]
fn wear_leveling_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["max_erase", "min_erase", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("balanced", i32_ty());
    // Wear leveling: max-min erase count difference should be below threshold
    ctx.push_obligation(ProofObligation::assume("mx", "max_erase == 520"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_erase == 480"));
    ctx.push_obligation(ProofObligation::assume("th", "threshold == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "b_def",
        "balanced == if max_erase - min_erase <= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "balanced == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "NAND controller: erase diff 40 ≤ 100 threshold → balanced",
    );
}

#[test]
fn read_retry_level() {
    let mut ctx = VerificationContext::new();
    for v in &["retry_level", "max_retry_level"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("retry_ok", i32_ty());
    // Read retry: adjust Vth sensing levels for worn cells
    ctx.push_obligation(ProofObligation::assume("rl", "retry_level == 3"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_retry_level == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "retry_ok == if retry_level <= max_retry_level { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "retry_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND controller: retry level 3 ≤ 7 max → OK");
}

#[test]
fn interface_timing() {
    let mut ctx = VerificationContext::new();
    for v in &["clock_mhz", "max_clock_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("timing_ok", i32_ty());
    // ONFI interface: up to 200MHz (DDR), 400MT/s
    ctx.push_obligation(ProofObligation::assume("cm", "clock_mhz == 100"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_clock_mhz == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "timing_ok == if clock_mhz <= max_clock_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "timing_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND controller: 100MHz ≤ 200MHz max → timing OK");
}

#[test]
fn cell_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bits_per_cell", u32_ty());
    ctx.declare_var_typed("is_tlc", i32_ty());
    // Cell types: 1=SLC, 2=MLC, 3=TLC, 4=QLC
    ctx.push_obligation(ProofObligation::assume("bc", "bits_per_cell == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "it_def",
        "is_tlc == if bits_per_cell == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_tlc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND controller: 3 bits/cell → TLC");
}
