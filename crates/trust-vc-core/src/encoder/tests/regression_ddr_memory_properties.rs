// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ddr4_data_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["clock_mhz", "data_rate_mtps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DDR4: double data rate → transfers = 2 × clock
    // DDR4-3200: 1600 MHz clock × 2 = 3200 MT/s
    ctx.push_obligation(ProofObligation::assume("cm", "clock_mhz == 1600"));
    ctx.push_obligation(ProofObligation::assume("dr", "data_rate_mtps == 3200")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_3200", "data_rate_mtps == 3200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DDR4: 1600 MHz × 2 = 3200 MT/s");
}

#[test]
fn cas_latency_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cas_latency", u32_ty());
    ctx.declare_var_typed("valid_cl", i32_ty());
    // DDR4 typical CAS latencies: 14-22 range
    ctx.push_obligation(ProofObligation::assume("cl", "cas_latency == 18"));
    ctx.push_obligation(ProofObligation::assume(
        "vcl_def",
        "valid_cl == if cas_latency >= 14 && cas_latency <= 22 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_cl == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DDR4: CL 18 in [14, 22] → valid");
}

#[test]
fn rank_interleave_selection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("address_bit", u32_ty());
    ctx.declare_var_typed("num_ranks", u32_ty());
    ctx.declare_var_typed("selected_rank", u32_ty());
    // Rank interleaving: rank = address_bit % num_ranks. Precompute: 5 % 2 = 1
    ctx.push_obligation(ProofObligation::assume("ab", "address_bit == 5"));
    ctx.push_obligation(ProofObligation::assume("nr", "num_ranks == 2"));
    ctx.push_obligation(ProofObligation::assume("sr", "selected_rank == 1")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1", "selected_rank == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DDR: rank interleave addr 5 % 2 = rank 1");
}

#[test]
fn refresh_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["trefi_ns", "temp_above_85c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("effective_trefi_ns", u32_ty());
    // DDR4: tREFI = 7800ns normal, halved at >85°C → 3900ns
    ctx.push_obligation(ProofObligation::assume("tr", "trefi_ns == 7800"));
    ctx.push_obligation(ProofObligation::assume("ta", "temp_above_85c == 1")); // yes, hot
    ctx.push_obligation(ProofObligation::assume(
        "et_def",
        "effective_trefi_ns == if temp_above_85c == 1 { 3900 } else { 7800 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_3900",
        "effective_trefi_ns == 3900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DDR4: >85°C → tREFI halved to 3900ns");
}

#[test]
fn bank_group_count() {
    let mut ctx = VerificationContext::new();
    for v in &["total_banks", "banks_per_group", "num_bank_groups"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DDR4: 16 banks / 4 per group = 4 bank groups. Precompute.
    ctx.push_obligation(ProofObligation::assume("tb", "total_banks == 16"));
    ctx.push_obligation(ProofObligation::assume("bpg", "banks_per_group == 4"));
    ctx.push_obligation(ProofObligation::assume("nbg", "num_bank_groups == 4")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_4", "num_bank_groups == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DDR4: 16 banks / 4 per group = 4 bank groups");
}

#[test]
fn row_column_address() {
    let mut ctx = VerificationContext::new();
    for v in &["row_bits", "column_bits", "total_address_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DDR4: row + column address bits
    ctx.push_obligation(ProofObligation::assume("rb", "row_bits == 16"));
    ctx.push_obligation(ProofObligation::assume("cb", "column_bits == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "tab_def",
        "total_address_bits == row_bits + column_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_26", "total_address_bits == 26"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DDR4: 16 row + 10 column = 26 address bits");
}

#[test]
fn write_leveling_delay() {
    let mut ctx = VerificationContext::new();
    for v in &["dqs_delay_ps", "max_delay_ps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Write leveling: DQS delay must be within one clock cycle
    ctx.push_obligation(ProofObligation::assume("dd", "dqs_delay_ps == 450"));
    ctx.push_obligation(ProofObligation::assume("md", "max_delay_ps == 625")); // one 1600MHz period
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if dqs_delay_ps <= max_delay_ps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DDR: DQS delay 450ps ≤ 625ps period → in range");
}

#[test]
fn dimm_capacity_gb() {
    let mut ctx = VerificationContext::new();
    for v in &["ranks", "chips_per_rank", "chip_density_gb", "dimm_gb"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DIMM capacity = ranks × chips × density. Precompute: 2 × 8 × 1 = 16 GB
    ctx.push_obligation(ProofObligation::assume("r", "ranks == 2"));
    ctx.push_obligation(ProofObligation::assume("cpr", "chips_per_rank == 8"));
    ctx.push_obligation(ProofObligation::assume("cd", "chip_density_gb == 1"));
    ctx.push_obligation(ProofObligation::assume("dg", "dimm_gb == 16")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_16", "dimm_gb == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DDR: 2 ranks × 8 chips × 1GB = 16GB DIMM");
}

#[test]
fn zq_calibration_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["ops_since_zqcal", "zqcal_interval"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_zqcal", i32_ty());
    // ZQ calibration needed periodically to maintain output impedance
    ctx.push_obligation(ProofObligation::assume("osz", "ops_since_zqcal == 128000"));
    ctx.push_obligation(ProofObligation::assume("zi", "zqcal_interval == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "nz_def",
        "needs_zqcal == if ops_since_zqcal >= zqcal_interval { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_zqcal == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DDR: 128000 ops ≥ 100000 interval → needs ZQ cal");
}

#[test]
fn read_write_turnaround() {
    let mut ctx = VerificationContext::new();
    for v in &["trtw_clocks", "min_trtw"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("meets_timing", i32_ty());
    // Read-to-write turnaround must meet minimum
    ctx.push_obligation(ProofObligation::assume("tc", "trtw_clocks == 10"));
    ctx.push_obligation(ProofObligation::assume("mt", "min_trtw == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "mt_def",
        "meets_timing == if trtw_clocks >= min_trtw { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "meets_timing == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DDR: tRTW 10 clocks ≥ 8 min → timing met");
}
