// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn hamming_code_parity_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bits", "parity_bits", "total_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Hamming(7,4): 4 data bits, 3 parity bits
    ctx.push_obligation(ProofObligation::assume("db", "data_bits == 4"));
    ctx.push_obligation(ProofObligation::assume("pb", "parity_bits == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bits == data_bits + parity_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_7", "total_bits == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Hamming(7,4): 4 + 3 = 7 total bits");
}

#[test]
fn secded_overhead() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bits", "check_bits", "overhead_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // SECDED for 64-bit data: 8 check bits (7 Hamming + 1 overall parity)
    ctx.push_obligation(ProofObligation::assume("db", "data_bits == 64"));
    ctx.push_obligation(ProofObligation::assume("cb", "check_bits == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "ob_def",
        "overhead_bits == check_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "overhead_bits == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "low_overhead",
        "check_bits < data_bits",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SECDED: 64-bit data + 8 check bits");
}

#[test]
fn single_bit_correction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("syndrome", u32_ty());
    ctx.declare_var_typed("error_detected", i32_ty());
    ctx.declare_var_typed("correctable", i32_ty());
    // Non-zero syndrome = error detected; single-bit = correctable
    ctx.push_obligation(ProofObligation::assume("s", "syndrome == 5")); // non-zero
    ctx.push_obligation(ProofObligation::assume(
        "ed_def",
        "error_detected == if syndrome != 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "correctable == if syndrome != 0 && syndrome <= 72 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("detected", "error_detected == 1"));
    ctx.push_obligation(ProofObligation::assert("fixable", "correctable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECC: syndrome=5 → detected + correctable");
}

#[test]
fn double_bit_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("syndrome", u32_ty());
    ctx.declare_var_typed("overall_parity", u32_ty());
    ctx.declare_var_typed("double_bit_error", i32_ty());
    // SECDED: syndrome non-zero + overall parity even → double-bit (uncorrectable)
    ctx.push_obligation(ProofObligation::assume("s", "syndrome == 3"));
    ctx.push_obligation(ProofObligation::assume("op", "overall_parity == 0")); // even parity
    ctx.push_obligation(ProofObligation::assume(
        "dbe_def",
        "double_bit_error == if syndrome != 0 && overall_parity == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "double_bit_error == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "SECDED: syndrome≠0 + parity even → double-bit error",
    );
}

#[test]
fn scrub_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["memory_mb", "scrub_rate_mb_per_sec", "scrub_time_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Full memory scrub: time = size / rate
    ctx.push_obligation(ProofObligation::assume("mm", "memory_mb == 4096")); // 4GB
    ctx.push_obligation(ProofObligation::assume(
        "sr",
        "scrub_rate_mb_per_sec == 512",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "st_def",
        "scrub_time_sec == memory_mb / scrub_rate_mb_per_sec",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "scrub_time_sec == 8")); // 4096/512
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ECC scrub: 4096MB / 512MB/s = 8 seconds");
}

#[test]
fn error_counter_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["corrected_errors", "threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("replace_dimm", i32_ty());
    // Too many corrected errors suggest impending failure
    ctx.push_obligation(ProofObligation::assume("ce", "corrected_errors == 100"));
    ctx.push_obligation(ProofObligation::assume("t", "threshold == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "rd_def",
        "replace_dimm == if corrected_errors > threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "replace_dimm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ECC: 100 corrected > 50 threshold → replace DIMM");
}

#[test]
fn word_width_with_ecc() {
    let mut ctx = VerificationContext::new();
    for v in &["data_width", "ecc_width", "bus_width"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DDR4 ECC: 64 data + 8 ECC = 72 bits total
    ctx.push_obligation(ProofObligation::assume("dw", "data_width == 64"));
    ctx.push_obligation(ProofObligation::assume("ew", "ecc_width == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "bw_def",
        "bus_width == data_width + ecc_width",
    ));
    ctx.push_obligation(ProofObligation::assert("is_72", "bus_width == 72"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DDR4 ECC: 64 + 8 = 72 bit bus");
}

#[test]
fn chipkill_redundancy() {
    let mut ctx = VerificationContext::new();
    for v in &["num_chips", "data_chips", "redundancy_chips"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("chipkill_capable", i32_ty());
    // Chipkill: survive one full chip failure
    ctx.push_obligation(ProofObligation::assume("nc", "num_chips == 18")); // 9 per rank × 2
    ctx.push_obligation(ProofObligation::assume("dc", "data_chips == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "rc_def",
        "redundancy_chips == num_chips - data_chips",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ck_def",
        "chipkill_capable == if redundancy_chips >= 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "redundancy_chips == 2"));
    ctx.push_obligation(ProofObligation::assert("yes", "chipkill_capable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Chipkill: 18 - 16 = 2 redundancy chips");
}

#[test]
fn address_interleaving() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "num_channels", "channel"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Channel interleaving: address mod num_channels
    ctx.push_obligation(ProofObligation::assume("a", "address == 4096"));
    ctx.push_obligation(ProofObligation::assume("nc", "num_channels == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ch_def",
        "channel == address % num_channels",
    ));
    ctx.push_obligation(ProofObligation::assert("is_0", "channel == 0")); // 4096 mod 2 = 0
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ECC: address 4096 mod 2 = channel 0");
}

#[test]
fn patrol_scrub_progress() {
    let mut ctx = VerificationContext::new();
    for v in &["rows_scrubbed", "total_rows"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("scrub_complete", i32_ty());
    ctx.declare_var_typed("new_rows_scrubbed", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rs", "rows_scrubbed == 8191"));
    ctx.push_obligation(ProofObligation::assume("tr", "total_rows == 8192"));
    ctx.push_obligation(ProofObligation::assume(
        "nrs_def",
        "new_rows_scrubbed == rows_scrubbed + 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "sc_def",
        "scrub_complete == if new_rows_scrubbed >= total_rows { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_8192",
        "new_rows_scrubbed == 8192",
    ));
    ctx.push_obligation(ProofObligation::assert("done", "scrub_complete == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "patrol scrub: 8191 + 1 = 8192 → complete");
}
