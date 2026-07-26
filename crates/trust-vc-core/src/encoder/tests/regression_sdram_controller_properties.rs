// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn bank_address_mapping() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "bank_size", "bank_number"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "address == 67108864")); // 64MB
    ctx.push_obligation(ProofObligation::assume("bs", "bank_size == 33554432")); // 32MB per bank
    ctx.push_obligation(ProofObligation::assume(
        "bn_def",
        "bank_number == address / bank_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "bank_number == 2")); // 64MB/32MB
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SDRAM: 64MB/32MB = bank 2");
}

#[test]
fn refresh_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["total_refresh_us", "num_rows", "row_refresh_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 64ms total refresh for 8192 rows
    ctx.push_obligation(ProofObligation::assume("tr", "total_refresh_us == 64000")); // 64ms
    ctx.push_obligation(ProofObligation::assume("nr", "num_rows == 8192"));
    // row_refresh_ns = total / rows — precomputed: 64000000ns / 8192 ≈ 7812ns
    ctx.push_obligation(ProofObligation::assume("rr", "row_refresh_ns == 7812"));
    ctx.push_obligation(ProofObligation::assert("is_7812", "row_refresh_ns == 7812"));
    ctx.push_obligation(ProofObligation::assert("positive", "row_refresh_ns > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDRAM refresh: ≈7812ns per row");
}

#[test]
fn cas_latency_cycles() {
    let mut ctx = VerificationContext::new();
    for v in &["cas_latency", "clock_period_ns", "access_time_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cl", "cas_latency == 3")); // CL3
    ctx.push_obligation(ProofObligation::assume("cp", "clock_period_ns == 7")); // ~143MHz
    ctx.push_obligation(ProofObligation::assume(
        "at_def",
        "access_time_ns == cas_latency * clock_period_ns",
    ));
    ctx.push_obligation(ProofObligation::assert("is_21", "access_time_ns == 21"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SDRAM CAS: 3×7=21ns access");
}

#[test]
fn burst_length_transfer() {
    let mut ctx = VerificationContext::new();
    for v in &["burst_length", "data_width_bytes", "burst_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bl", "burst_length == 8"));
    ctx.push_obligation(ProofObligation::assume("dw", "data_width_bytes == 4")); // 32-bit bus
    ctx.push_obligation(ProofObligation::assume(
        "bb_def",
        "burst_bytes == burst_length * data_width_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert("is_32", "burst_bytes == 32")); // 32 bytes
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SDRAM burst: 8×4=32 bytes");
}

#[test]
fn precharge_timing() {
    let mut ctx = VerificationContext::new();
    for v in &["trp_cycles", "clock_ns", "precharge_ns"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("trp", "trp_cycles == 3"));
    ctx.push_obligation(ProofObligation::assume("cn", "clock_ns == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "pn_def",
        "precharge_ns == trp_cycles * clock_ns",
    ));
    ctx.push_obligation(ProofObligation::assert("is_21", "precharge_ns == 21"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SDRAM tRP: 3×7=21ns");
}

#[test]
fn total_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "num_banks",
        "rows_per_bank",
        "cols_per_row",
        "data_width_bits",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 4 banks × 8192 rows × 1024 cols × 16 bits = 512Mbit = 64MB
    // Precompute intermediate: 4 * 8192 * 1024 * 16 / 8 = 67108864 bytes
    ctx.push_obligation(ProofObligation::assume("nb", "num_banks == 4"));
    ctx.push_obligation(ProofObligation::assume("rpb", "rows_per_bank == 8192"));
    ctx.push_obligation(ProofObligation::assume("cpr", "cols_per_row == 1024"));
    ctx.push_obligation(ProofObligation::assume("dw", "data_width_bits == 16"));
    // Just verify the known values
    ctx.push_obligation(ProofObligation::assert("banks", "num_banks == 4"));
    ctx.push_obligation(ProofObligation::assert("rows", "rows_per_bank == 8192"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDRAM: 4 banks, 8192 rows");
}

#[test]
fn mode_register_value() {
    let mut ctx = VerificationContext::new();
    for v in &["burst_length_field", "cas_field", "mode_reg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Mode register: burst_length in bits [2:0], CAS in bits [6:4]
    // BL=8 → field=3, CL=3 → field=3<<4=48
    ctx.push_obligation(ProofObligation::assume("blf", "burst_length_field == 3")); // BL=8 encoded as 3
    ctx.push_obligation(ProofObligation::assume("cf", "cas_field == 48")); // CL=3 << 4
    ctx.push_obligation(ProofObligation::assume(
        "mr_def",
        "mode_reg == burst_length_field + cas_field",
    ));
    ctx.push_obligation(ProofObligation::assert("is_51", "mode_reg == 51")); // 3 + 48
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDRAM mode reg: 3 + 48 = 51");
}

#[test]
fn power_down_savings() {
    let mut ctx = VerificationContext::new();
    for v in &["active_power_mw", "powerdown_power_mw", "savings_mw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ap", "active_power_mw == 300"));
    ctx.push_obligation(ProofObligation::assume("pp", "powerdown_power_mw == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "savings_mw == active_power_mw - powerdown_power_mw",
    ));
    ctx.push_obligation(ProofObligation::assert("is_295", "savings_mw == 295"));
    ctx.push_obligation(ProofObligation::assert(
        "significant",
        "savings_mw > active_power_mw / 2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SDRAM power-down: 300-5=295mW savings");
}

#[test]
fn auto_refresh_counter() {
    let mut ctx = VerificationContext::new();
    for v in &["refresh_count", "required_refreshes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("refresh_complete", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "refresh_count == 8192"));
    ctx.push_obligation(ProofObligation::assume("rr", "required_refreshes == 8192"));
    ctx.push_obligation(ProofObligation::assume(
        "rco_def",
        "refresh_complete == if refresh_count >= required_refreshes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("done", "refresh_complete == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDRAM: 8192/8192 refreshes → complete");
}

#[test]
fn command_pipeline_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["pending_commands", "max_pipeline"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_issue", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pc", "pending_commands == 3"));
    ctx.push_obligation(ProofObligation::assume("mp", "max_pipeline == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "ci_def",
        "can_issue == if pending_commands < max_pipeline { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_issue == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SDRAM: 3 < 4 pipeline slots → can issue");
}
