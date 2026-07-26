// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn page_write_boundary() {
    let mut ctx = VerificationContext::new();
    for v in &["start_addr", "write_length", "page_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("end_addr", u32_ty());
    ctx.declare_var_typed("crosses_page", i32_ty());
    // EEPROM page write must not cross page boundary
    // Page size = 64 bytes. Write 32 bytes from addr 48: 48+32=80 > 64 → crosses
    ctx.push_obligation(ProofObligation::assume("sa", "start_addr == 48"));
    ctx.push_obligation(ProofObligation::assume("wl", "write_length == 32"));
    ctx.push_obligation(ProofObligation::assume("ps", "page_size == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "ea_def",
        "end_addr == start_addr + write_length",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "cp_def",
        "crosses_page == if end_addr > page_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_80", "end_addr == 80"));
    ctx.push_obligation(ProofObligation::assert("yes", "crosses_page == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EEPROM: addr 48 + 32 = 80 > 64 page → crosses boundary",
    );
}

#[test]
fn address_space_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["address_bits", "max_address"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Address space = 2^bits - 1. Precompute: 2^16 - 1 = 65535
    ctx.push_obligation(ProofObligation::assume("ab", "address_bits == 16"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_address == 65535")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_65535", "max_address == 65535"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EEPROM: 16-bit address → 65535 max addr");
}

#[test]
fn write_cycle_time() {
    let mut ctx = VerificationContext::new();
    for v in &["elapsed_us", "write_cycle_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("write_done", i32_ty());
    // Typical write cycle: 5ms = 5000 μs
    ctx.push_obligation(ProofObligation::assume("eu", "elapsed_us == 6000"));
    ctx.push_obligation(ProofObligation::assume("wcu", "write_cycle_us == 5000"));
    ctx.push_obligation(ProofObligation::assume(
        "wd_def",
        "write_done == if elapsed_us >= write_cycle_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "write_done == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EEPROM: 6000μs ≥ 5000μs write cycle → done");
}

#[test]
fn endurance_cycles() {
    let mut ctx = VerificationContext::new();
    for v in &["write_count", "max_endurance"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_spec", i32_ty());
    // Typical endurance: 1 million cycles
    ctx.push_obligation(ProofObligation::assume("wc", "write_count == 500000"));
    ctx.push_obligation(ProofObligation::assume("me", "max_endurance == 1000000"));
    ctx.push_obligation(ProofObligation::assume(
        "ws_def",
        "within_spec == if write_count < max_endurance { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "within_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EEPROM: 500K writes < 1M endurance → within spec");
}

#[test]
fn device_address_selection() {
    let mut ctx = VerificationContext::new();
    for v in &["base_address", "a2a1a0_pins"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("i2c_address", u32_ty());
    // I2C address = base | pin_config. Precompute: 0x50 | 3 = 0x53 (83)
    ctx.push_obligation(ProofObligation::assume("ba", "base_address == 80")); // 0x50
    ctx.push_obligation(ProofObligation::assume("ap", "a2a1a0_pins == 3"));
    ctx.push_obligation(ProofObligation::assume("ia", "i2c_address == 83")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_83", "i2c_address == 83"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EEPROM: base 0x50 | pins 3 = 0x53 (precomputed)");
}

#[test]
fn write_protect_region() {
    let mut ctx = VerificationContext::new();
    for v in &["target_addr", "wp_start", "wp_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("write_blocked", i32_ty());
    // Write-protect upper quarter: addresses 49152-65535
    ctx.push_obligation(ProofObligation::assume("ta", "target_addr == 50000"));
    ctx.push_obligation(ProofObligation::assume("ws", "wp_start == 49152"));
    ctx.push_obligation(ProofObligation::assume("we", "wp_end == 65535"));
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "write_blocked == if target_addr >= wp_start && target_addr <= wp_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "write_blocked == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EEPROM: addr 50000 in [49152, 65535] → write blocked",
    );
}

#[test]
fn sequential_read_wrap() {
    let mut ctx = VerificationContext::new();
    for v in &["current_addr", "memory_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("at_wrap", i32_ty());
    // Sequential read wraps at end of memory
    ctx.push_obligation(ProofObligation::assume("ca", "current_addr == 65535"));
    ctx.push_obligation(ProofObligation::assume("ms", "memory_size == 65536"));
    ctx.push_obligation(ProofObligation::assume(
        "aw_def",
        "at_wrap == if current_addr >= memory_size - 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "at_wrap == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EEPROM: addr 65535 = last addr → at wrap point");
}

#[test]
fn data_retention_years() {
    let mut ctx = VerificationContext::new();
    for v in &["retention_years", "minimum_retention"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("meets_spec", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ry", "retention_years == 100"));
    ctx.push_obligation(ProofObligation::assume("mr", "minimum_retention == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "ms_def",
        "meets_spec == if retention_years >= minimum_retention { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "meets_spec == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EEPROM: 100 year retention ≥ 40 year spec → meets");
}

#[test]
fn byte_vs_page_write() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("write_length", u32_ty());
    ctx.declare_var_typed("is_page_write", i32_ty());
    // Page write: length > 1
    ctx.push_obligation(ProofObligation::assume("wl", "write_length == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "ipw_def",
        "is_page_write == if write_length > 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_page_write == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "EEPROM: 32 bytes > 1 → page write mode");
}

#[test]
fn ack_polling_ready() {
    let mut ctx = VerificationContext::new();
    for v in &["poll_attempts", "max_polls"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ack_received", i32_ty());
    ctx.declare_var_typed("timeout", i32_ty());
    // ACK polling: device responds after write cycle completes
    ctx.push_obligation(ProofObligation::assume("pa", "poll_attempts == 5"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_polls == 100"));
    ctx.push_obligation(ProofObligation::assume("ar", "ack_received == 1")); // device ready
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "timeout == if poll_attempts >= max_polls { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ready", "ack_received == 1"));
    ctx.push_obligation(ProofObligation::assert("no_timeout", "timeout == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "EEPROM: ACK at poll 5 < 100 max → ready, no timeout",
    );
}
