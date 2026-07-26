// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn codeword_length() {
    let mut ctx = VerificationContext::new();
    for v in &["data_symbols", "parity_symbols", "codeword_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ds", "data_symbols == 223"));
    ctx.push_obligation(ProofObligation::assume("ps", "parity_symbols == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "cl_def",
        "codeword_len == data_symbols + parity_symbols",
    ));
    ctx.push_obligation(ProofObligation::assert("is_255", "codeword_len == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS(255,223): 223 + 32 = 255");
}

#[test]
fn error_correction_capacity() {
    // t = parity_symbols / 2
    let mut ctx = VerificationContext::new();
    for v in &["parity_symbols", "correction_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "parity_symbols == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "cc_def",
        "correction_capacity == parity_symbols / 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_16",
        "correction_capacity == 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RS: 32 parity / 2 = 16 correctable errors");
}

#[test]
fn erasure_correction_capacity() {
    // Can correct up to parity_symbols erasures (known positions)
    let mut ctx = VerificationContext::new();
    for v in &["parity_symbols", "erasure_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "parity_symbols == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "ec_def",
        "erasure_capacity == parity_symbols",
    ));
    ctx.push_obligation(ProofObligation::assert("is_32", "erasure_capacity == 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS: erasure capacity = parity symbols = 32");
}

#[test]
fn mixed_error_erasure_bound() {
    // 2*errors + erasures <= parity_symbols
    let mut ctx = VerificationContext::new();
    for v in &["errors", "erasures", "parity_symbols", "used_capacity"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_bound", i32_ty());
    ctx.push_obligation(ProofObligation::assume("e", "errors == 5"));
    ctx.push_obligation(ProofObligation::assume("er", "erasures == 10"));
    ctx.push_obligation(ProofObligation::assume("ps", "parity_symbols == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "uc_def",
        "used_capacity == 2 * errors + erasures",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "within_bound == if used_capacity <= parity_symbols { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_20", "used_capacity == 20"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_bound == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RS: 2*5 + 10 = 20 <= 32 parity");
}

#[test]
fn code_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["data_symbols", "codeword_len", "rate_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ds", "data_symbols == 223"));
    ctx.push_obligation(ProofObligation::assume("cl", "codeword_len == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "rp_def",
        "rate_pct == data_symbols * 100 / codeword_len",
    ));
    ctx.push_obligation(ProofObligation::assert("is_87", "rate_pct == 87")); // 223/255 ≈ 87%
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RS code rate: 223*100/255 ≈ 87%");
}

#[test]
fn minimum_distance() {
    // d_min = parity_symbols + 1
    let mut ctx = VerificationContext::new();
    for v in &["parity_symbols", "min_distance"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "parity_symbols == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "md_def",
        "min_distance == parity_symbols + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_33", "min_distance == 33"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS minimum distance: 32 + 1 = 33");
}

#[test]
fn syndrome_count() {
    let mut ctx = VerificationContext::new();
    for v in &["parity_symbols", "syndromes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "parity_symbols == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "syndromes == parity_symbols",
    ));
    ctx.push_obligation(ProofObligation::assert("is_32", "syndromes == 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RS: syndromes = parity = 32");
}

#[test]
fn shortened_code() {
    // RS(255,223) shortened to RS(200,168): remove 55 data symbols
    let mut ctx = VerificationContext::new();
    for v in &[
        "original_data",
        "shortened_by",
        "new_data",
        "parity",
        "new_codeword",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("od", "original_data == 223"));
    ctx.push_obligation(ProofObligation::assume("sb", "shortened_by == 55"));
    ctx.push_obligation(ProofObligation::assume(
        "nd_def",
        "new_data == original_data - shortened_by",
    ));
    ctx.push_obligation(ProofObligation::assume("p", "parity == 32")); // parity unchanged
    ctx.push_obligation(ProofObligation::assume(
        "nc_def",
        "new_codeword == new_data + parity",
    ));
    ctx.push_obligation(ProofObligation::assert("nd_168", "new_data == 168"));
    ctx.push_obligation(ProofObligation::assert("nc_200", "new_codeword == 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shortened RS: 223-55=168 data, 168+32=200 codeword",
    );
}

#[test]
fn interleaving_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["burst_length", "symbol_size", "interleave_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bl", "burst_length == 128")); // burst error length in bits
    ctx.push_obligation(ProofObligation::assume("ss", "symbol_size == 8")); // 8 bits per symbol
    ctx.push_obligation(ProofObligation::assume(
        "id_def",
        "interleave_depth == burst_length / symbol_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "interleave_depth == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "interleave: 128-bit burst / 8-bit symbol = depth 16",
    );
}

#[test]
fn redundancy_overhead() {
    let mut ctx = VerificationContext::new();
    for v in &["parity_symbols", "data_symbols", "overhead_pct"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "parity_symbols == 32"));
    ctx.push_obligation(ProofObligation::assume("ds", "data_symbols == 223"));
    ctx.push_obligation(ProofObligation::assume(
        "op_def",
        "overhead_pct == parity_symbols * 100 / data_symbols",
    ));
    ctx.push_obligation(ProofObligation::assert("is_14", "overhead_pct == 14")); // 32/223 ≈ 14%
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RS overhead: 32*100/223 ≈ 14%");
}
