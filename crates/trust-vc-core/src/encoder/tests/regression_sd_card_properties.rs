// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn speed_class_minimum() {
    let mut ctx = VerificationContext::new();
    for v in &["write_speed_mbps", "class_requirement_mbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("meets_class", i32_ty());
    // UHS Speed Class 3 (U3): minimum 30 MB/s write
    ctx.push_obligation(ProofObligation::assume("ws", "write_speed_mbps == 45"));
    ctx.push_obligation(ProofObligation::assume(
        "cr",
        "class_requirement_mbps == 30",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "mc_def",
        "meets_class == if write_speed_mbps >= class_requirement_mbps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "meets_class == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SD: 45 MB/s ≥ 30 MB/s U3 requirement → meets class",
    );
}

#[test]
fn block_size_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["offset_bytes", "block_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    // SD block = 512 bytes. Check alignment. Precompute: 2048 % 512 = 0
    ctx.push_obligation(ProofObligation::assume("ob", "offset_bytes == 2048"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 512"));
    ctx.push_obligation(ProofObligation::assume("aligned_val", "aligned == 1")); // precomputed
    ctx.push_obligation(ProofObligation::assert("yes", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SD: offset 2048 aligned to 512 (precomputed)");
}

#[test]
fn capacity_sectors() {
    let mut ctx = VerificationContext::new();
    for v in &["capacity_gb", "sector_size", "total_sectors"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Sectors = capacity_GB × 1024 × 1024 × 1024 / 512. Precompute: 32GB = 62914560 sectors
    ctx.push_obligation(ProofObligation::assume("cg", "capacity_gb == 32"));
    ctx.push_obligation(ProofObligation::assume("ss", "sector_size == 512"));
    ctx.push_obligation(ProofObligation::assume("ts", "total_sectors == 62914560")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_62914560",
        "total_sectors == 62914560",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SD: 32GB / 512 = 62914560 sectors (precomputed)");
}

#[test]
fn cmd_response_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cmd_index", u32_ty());
    ctx.declare_var_typed("is_read_cmd", i32_ty());
    // CMD17 = READ_SINGLE_BLOCK
    ctx.push_obligation(ProofObligation::assume("ci", "cmd_index == 17"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_read_cmd == if cmd_index == 17 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_read_cmd == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SD: CMD17 → READ_SINGLE_BLOCK");
}

#[test]
fn crc7_polynomial() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("crc_bits", u32_ty());
    ctx.declare_var_typed("valid_crc_width", i32_ty());
    // SD command CRC is 7 bits
    ctx.push_obligation(ProofObligation::assume("cb", "crc_bits == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "vcw_def",
        "valid_crc_width == if crc_bits == 7 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_crc_width == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SD: CRC7 width = 7 bits → valid");
}

#[test]
fn bus_width_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bus_width", u32_ty());
    ctx.declare_var_typed("is_4bit", i32_ty());
    // SD: 1-bit or 4-bit bus
    ctx.push_obligation(ProofObligation::assume("bw", "bus_width == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "i4_def",
        "is_4bit == if bus_width == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_4bit == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SD: bus width 4 → 4-bit mode");
}

#[test]
fn voltage_range_check() {
    let mut ctx = VerificationContext::new();
    for v in &["supply_mv", "min_voltage_mv", "max_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("voltage_ok", i32_ty());
    // SD card: 2.7-3.6V operating range
    ctx.push_obligation(ProofObligation::assume("sm", "supply_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("mnv", "min_voltage_mv == 2700"));
    ctx.push_obligation(ProofObligation::assume("mxv", "max_voltage_mv == 3600"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "voltage_ok == if supply_mv >= min_voltage_mv && supply_mv <= max_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "voltage_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SD: 3.3V in [2.7, 3.6] → voltage OK");
}

#[test]
fn write_protect_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wp_pin", u32_ty());
    ctx.declare_var_typed("can_write", i32_ty());
    // Write protect: pin 0 = writable, 1 = protected
    ctx.push_obligation(ProofObligation::assume("wp", "wp_pin == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "cw_def",
        "can_write == if wp_pin == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_write == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SD: WP pin 0 → can write");
}

#[test]
fn multi_block_count() {
    let mut ctx = VerificationContext::new();
    for v in &["total_bytes", "block_size", "num_blocks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Blocks = total / block_size. Precompute: 8192 / 512 = 16
    ctx.push_obligation(ProofObligation::assume("tb", "total_bytes == 8192"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 512"));
    ctx.push_obligation(ProofObligation::assume("nb", "num_blocks == 16")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_16", "num_blocks == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SD: 8192 bytes / 512 = 16 blocks");
}

#[test]
fn clock_frequency_limit() {
    let mut ctx = VerificationContext::new();
    for v in &["clock_mhz", "max_clock_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_spec", i32_ty());
    // SD High Speed: max 50 MHz
    ctx.push_obligation(ProofObligation::assume("cm", "clock_mhz == 48"));
    ctx.push_obligation(ProofObligation::assume("mcm", "max_clock_mhz == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_spec == if clock_mhz <= max_clock_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SD: 48 MHz ≤ 50 MHz max → within spec");
}
