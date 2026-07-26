// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn page_size_with_oob() {
    let mut ctx = VerificationContext::new();
    for v in &["data_bytes", "oob_bytes", "total_page_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // NAND page: 4096 data + 224 OOB = 4320 total
    ctx.push_obligation(ProofObligation::assume("db", "data_bytes == 4096"));
    ctx.push_obligation(ProofObligation::assume("ob", "oob_bytes == 224"));
    ctx.push_obligation(ProofObligation::assume(
        "tp_def",
        "total_page_bytes == data_bytes + oob_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_4320",
        "total_page_bytes == 4320",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND: 4096 data + 224 OOB = 4320 total page");
}

#[test]
fn block_page_count() {
    let mut ctx = VerificationContext::new();
    for v in &["pages_per_block", "block_number", "first_page"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // First page of block N = N × pages_per_block. Precompute.
    ctx.push_obligation(ProofObligation::assume("ppb", "pages_per_block == 64"));
    ctx.push_obligation(ProofObligation::assume("bn", "block_number == 10"));
    ctx.push_obligation(ProofObligation::assume("fp", "first_page == 640")); // precomputed 10×64
    ctx.push_obligation(ProofObligation::assert("is_640", "first_page == 640"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND: block 10 × 64 pages/block = page 640");
}

#[test]
fn wear_leveling_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["erase_count", "max_erase_cycles"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("worn_out", i32_ty());
    // Block worn out when erase count reaches max
    ctx.push_obligation(ProofObligation::assume("ec", "erase_count == 95000"));
    ctx.push_obligation(ProofObligation::assume("mec", "max_erase_cycles == 100000"));
    ctx.push_obligation(ProofObligation::assume(
        "wo_def",
        "worn_out == if erase_count >= max_erase_cycles { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "worn_out == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND: 95000 erases < 100000 max → not worn out");
}

#[test]
fn bad_block_table_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["bad_blocks", "max_bad_blocks"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("table_full", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bb", "bad_blocks == 40"));
    ctx.push_obligation(ProofObligation::assume("mbb", "max_bad_blocks == 80"));
    ctx.push_obligation(ProofObligation::assume(
        "tf_def",
        "table_full == if bad_blocks >= max_bad_blocks { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no", "table_full == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND BBT: 40 bad < 80 max → table not full");
}

#[test]
fn ecc_correction_capability() {
    let mut ctx = VerificationContext::new();
    for v in &["bit_errors", "ecc_strength"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("correctable", i32_ty());
    // BCH ECC: correctable if errors ≤ ECC strength
    ctx.push_obligation(ProofObligation::assume("be", "bit_errors == 6"));
    ctx.push_obligation(ProofObligation::assume("es", "ecc_strength == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "correctable == if bit_errors <= ecc_strength { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "correctable == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND ECC: 6 errors ≤ 8 BCH strength → correctable");
}

#[test]
fn program_disturb_distance() {
    let mut ctx = VerificationContext::new();
    for v in &["target_page", "last_read_page"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("distance", u32_ty());
    ctx.declare_var_typed("safe", i32_ty());
    // Program disturb: pages far apart in same block are safer
    ctx.push_obligation(ProofObligation::assume("tp", "target_page == 50"));
    ctx.push_obligation(ProofObligation::assume("lrp", "last_read_page == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "distance == target_page - last_read_page",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "safe == if distance > 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40", "distance == 40"));
    ctx.push_obligation(ProofObligation::assert("yes", "safe == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "NAND: page distance 50-10=40 > 8 → safe from disturb",
    );
}

#[test]
fn read_retry_count() {
    let mut ctx = VerificationContext::new();
    for v in &["retry_count", "max_retries"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("can_retry", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rc", "retry_count == 3"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_retries == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "cr_def",
        "can_retry == if retry_count < max_retries { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "can_retry == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND: retry 3 < 7 max → can retry");
}

#[test]
fn plane_interleave() {
    let mut ctx = VerificationContext::new();
    for v in &["num_planes", "block_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("plane_id", u32_ty());
    // Plane = block_id % num_planes. Precompute: 101 % 2 = 1
    ctx.push_obligation(ProofObligation::assume("np", "num_planes == 2"));
    ctx.push_obligation(ProofObligation::assume("bi", "block_id == 101"));
    ctx.push_obligation(ProofObligation::assume("pi", "plane_id == 1")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1", "plane_id == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND: block 101 % 2 planes = plane 1");
}

#[test]
fn cache_program_pipeline() {
    let mut ctx = VerificationContext::new();
    for v in &["page_program_us", "cache_load_us", "total_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_budget", i32_ty());
    // Cache program: overlap transfer with programming
    // Effective time = max(program, load). Precompute: program dominates.
    ctx.push_obligation(ProofObligation::assume("pp", "page_program_us == 1300"));
    ctx.push_obligation(ProofObligation::assume("cl", "cache_load_us == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total_us == if page_program_us > cache_load_us { page_program_us } else { cache_load_us }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "within_budget == if total_us <= 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1300", "total_us == 1300"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_budget == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND cache: max(1300, 100) = 1300us ≤ 2ms budget");
}

#[test]
fn ftl_mapping_table_size() {
    let mut ctx = VerificationContext::new();
    for v in &["logical_pages", "entry_bytes", "table_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // FTL map: logical_pages × entry_bytes. Precompute: 65536 × 4 = 262144
    ctx.push_obligation(ProofObligation::assume("lp", "logical_pages == 65536"));
    ctx.push_obligation(ProofObligation::assume("eb", "entry_bytes == 4"));
    ctx.push_obligation(ProofObligation::assume("tb", "table_bytes == 262144")); // precomputed
    ctx.push_obligation(ProofObligation::assert(
        "is_262144",
        "table_bytes == 262144",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NAND FTL: 65536 pages × 4 bytes = 262144 byte map");
}
