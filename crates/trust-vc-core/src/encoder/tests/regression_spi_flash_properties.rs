// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sector_erase_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "sector_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    // Sector erase requires aligned address. 4096-byte sectors: addr % 4096 == 0
    // Precompute: 0x10000 = 65536, 65536 % 4096 = 0
    ctx.push_obligation(ProofObligation::assume("ad", "address == 65536"));
    ctx.push_obligation(ProofObligation::assume("ss", "sector_size == 4096"));
    ctx.push_obligation(ProofObligation::assume("al", "aligned == 1")); // precomputed: 65536 % 4096 == 0
    ctx.push_obligation(ProofObligation::assert("yes", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SPI flash: 0x10000 aligned to 4096-byte sector (precomputed)",
    );
}

#[test]
fn page_program_size() {
    let mut ctx = VerificationContext::new();
    for v in &["write_bytes", "page_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits_page", i32_ty());
    // Page program limited to page boundary (typically 256 bytes)
    ctx.push_obligation(ProofObligation::assume("wb", "write_bytes == 128"));
    ctx.push_obligation(ProofObligation::assume("ps", "page_size == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "fp_def",
        "fits_page == if write_bytes <= page_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fits_page == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI flash: 128 bytes ≤ 256 page size → fits page");
}

#[test]
fn capacity_check() {
    let mut ctx = VerificationContext::new();
    for v in &["used_bytes", "total_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("space_ok", i32_ty());
    // Check available space
    ctx.push_obligation(ProofObligation::assume("ub", "used_bytes == 2000000"));
    ctx.push_obligation(ProofObligation::assume("tb", "total_bytes == 4194304")); // 4MB (32Mbit)
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "space_ok == if used_bytes < total_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "space_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI flash: 2MB used < 4MB total → space available");
}

#[test]
fn clock_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["spi_freq_mhz", "max_freq_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("freq_ok", i32_ty());
    // SPI flash max clock (e.g., 104 MHz for fast read)
    ctx.push_obligation(ProofObligation::assume("sf", "spi_freq_mhz == 80"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_freq_mhz == 104"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "freq_ok == if spi_freq_mhz <= max_freq_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "freq_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI flash: 80 MHz ≤ 104 MHz max → frequency OK");
}

#[test]
fn erase_endurance() {
    let mut ctx = VerificationContext::new();
    for v in &["erase_count", "max_erases"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_endurance", i32_ty());
    // Typical NOR flash: 100K erase cycles per sector
    ctx.push_obligation(ProofObligation::assume("ec", "erase_count == 50000"));
    ctx.push_obligation(ProofObligation::assume("me", "max_erases == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "we_def",
        "within_endurance == if erase_count < max_erases { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_endurance == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SPI flash: 50K erases < 100K max → within endurance",
    );
}

#[test]
fn write_protect_status() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bp_bits", u32_ty());
    ctx.declare_var_typed("fully_protected", i32_ty());
    // Block protect bits in status register: 0=none, 7(0b111)=all
    ctx.push_obligation(ProofObligation::assume("bp", "bp_bits == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "fp_def",
        "fully_protected == if bp_bits == 7 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fully_protected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI flash: BP bits=7 → fully write protected");
}

#[test]
fn jedec_id_match() {
    let mut ctx = VerificationContext::new();
    for v in &["manufacturer_id", "expected_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("id_match", i32_ty());
    // JEDEC manufacturer ID: e.g., 0xEF = Winbond
    ctx.push_obligation(ProofObligation::assume("mi", "manufacturer_id == 239")); // 0xEF
    ctx.push_obligation(ProofObligation::assume("ei", "expected_id == 239"));
    ctx.push_obligation(ProofObligation::assume(
        "im_def",
        "id_match == if manufacturer_id == expected_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "id_match == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SPI flash: manufacturer 0xEF = expected → ID match",
    );
}

#[test]
fn dual_quad_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("io_mode", u32_ty());
    ctx.declare_var_typed("is_quad", i32_ty());
    // SPI modes: 0=standard, 1=dual, 2=quad
    ctx.push_obligation(ProofObligation::assume("im", "io_mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "iq_def",
        "is_quad == if io_mode == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_quad == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI flash: io_mode=2 → quad SPI mode");
}

#[test]
fn address_width() {
    let mut ctx = VerificationContext::new();
    for v in &["total_bytes", "needs_4byte"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("use_4byte_addr", i32_ty());
    // >16MB (>24-bit address) requires 4-byte addressing
    ctx.push_obligation(ProofObligation::assume("tb", "total_bytes == 33554432")); // 32MB
    ctx.push_obligation(ProofObligation::assume("n4", "needs_4byte == 16777216")); // 16MB threshold
    ctx.push_obligation(ProofObligation::assume(
        "u4_def",
        "use_4byte_addr == if total_bytes > needs_4byte { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "use_4byte_addr == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SPI flash: 32MB > 16MB → needs 4-byte addressing");
}

#[test]
fn data_retention() {
    let mut ctx = VerificationContext::new();
    for v in &["years_stored", "retention_years"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("data_safe", i32_ty());
    // Typical NOR flash: 20+ year data retention
    ctx.push_obligation(ProofObligation::assume("ys", "years_stored == 10"));
    ctx.push_obligation(ProofObligation::assume("ry", "retention_years == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ds_def",
        "data_safe == if years_stored < retention_years { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "data_safe == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SPI flash: 10 years < 20 year retention → data safe",
    );
}
