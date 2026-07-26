// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn inner_join_result_bounded() {
    let mut ctx = VerificationContext::new();
    for v in &["left_rows", "right_rows", "result_rows"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lr", "left_rows == 100"));
    ctx.push_obligation(ProofObligation::assume("rr", "right_rows == 200"));
    ctx.push_obligation(ProofObligation::assume("res", "result_rows == 80")); // matching rows
    ctx.push_obligation(ProofObligation::assert(
        "bounded_left",
        "result_rows <= left_rows",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded_right",
        "result_rows <= right_rows",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inner join: 80 results <= min(100, 200)");
}

#[test]
fn cross_join_cardinality() {
    let mut ctx = VerificationContext::new();
    for v in &["left_rows", "right_rows", "result_rows"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lr", "left_rows == 10"));
    ctx.push_obligation(ProofObligation::assume("rr", "right_rows == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "res_def",
        "result_rows == left_rows * right_rows",
    ));
    ctx.push_obligation(ProofObligation::assert("is_200", "result_rows == 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "cross join: 10 * 20 = 200 rows");
}

#[test]
fn left_join_preserves_left() {
    let mut ctx = VerificationContext::new();
    for v in &["left_rows", "result_rows"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lr", "left_rows == 100"));
    ctx.push_obligation(ProofObligation::assume("res", "result_rows == 100")); // at least left count
    ctx.push_obligation(ProofObligation::assert(
        "preserves",
        "result_rows >= left_rows",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "left join: result >= left rows");
}

#[test]
fn nested_loop_join_comparisons() {
    let mut ctx = VerificationContext::new();
    for v in &["outer_rows", "inner_rows", "comparisons"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("or", "outer_rows == 100"));
    ctx.push_obligation(ProofObligation::assume("ir", "inner_rows == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "comparisons == outer_rows * inner_rows",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_100000",
        "comparisons == 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "NLJ: 100 * 1000 = 100000 comparisons");
}

#[test]
fn hash_join_build_phase() {
    let mut ctx = VerificationContext::new();
    for v in &["build_rows", "hash_buckets", "avg_chain_length"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("br", "build_rows == 1000"));
    ctx.push_obligation(ProofObligation::assume("hb", "hash_buckets == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "acl_def",
        "avg_chain_length == build_rows / hash_buckets",
    ));
    ctx.push_obligation(ProofObligation::assert("is_10", "avg_chain_length == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "hash join: 1000 rows / 100 buckets = 10 avg chain");
}

#[test]
fn sort_merge_join_total_cost() {
    let mut ctx = VerificationContext::new();
    for v in &["sort_left", "sort_right", "merge_cost", "total_cost"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sl", "sort_left == 500")); // sort cost
    ctx.push_obligation(ProofObligation::assume("sr", "sort_right == 800"));
    ctx.push_obligation(ProofObligation::assume("mc", "merge_cost == 200")); // linear merge
    ctx.push_obligation(ProofObligation::assume(
        "tc_def",
        "total_cost == sort_left + sort_right + merge_cost",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1500", "total_cost == 1500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sort-merge: 500+800+200 = 1500 cost");
}

#[test]
fn index_lookup_selectivity() {
    let mut ctx = VerificationContext::new();
    for v in &["total_rows", "selectivity_pct", "expected_rows"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tr", "total_rows == 10000"));
    ctx.push_obligation(ProofObligation::assume("sp", "selectivity_pct == 5")); // 5%
    ctx.push_obligation(ProofObligation::assume(
        "er_def",
        "expected_rows == total_rows * selectivity_pct / 100",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "expected_rows == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "index: 10000 * 5% = 500 rows");
}

#[test]
fn semi_join_deduplicates() {
    let mut ctx = VerificationContext::new();
    for v in &["left_rows", "matching_distinct", "result_rows"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lr", "left_rows == 100"));
    ctx.push_obligation(ProofObligation::assume("md", "matching_distinct == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "res_def",
        "result_rows == matching_distinct",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "result_rows <= left_rows",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40", "result_rows == 40"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "semi-join: 40 distinct matches from 100 left");
}

#[test]
fn anti_join_complement() {
    let mut ctx = VerificationContext::new();
    for v in &["left_rows", "matching_rows", "anti_result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lr", "left_rows == 100"));
    ctx.push_obligation(ProofObligation::assume("mr", "matching_rows == 40"));
    ctx.push_obligation(ProofObligation::assume(
        "ar_def",
        "anti_result == left_rows - matching_rows",
    ));
    ctx.push_obligation(ProofObligation::assert("is_60", "anti_result == 60"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "anti-join: 100 - 40 matching = 60 non-matching");
}

#[test]
fn join_memory_budget() {
    let mut ctx = VerificationContext::new();
    for v in &["hash_table_size", "probe_buffer", "total_memory", "budget"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_budget", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hts", "hash_table_size == 5000"));
    ctx.push_obligation(ProofObligation::assume("pb", "probe_buffer == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "tm_def",
        "total_memory == hash_table_size + probe_buffer",
    ));
    ctx.push_obligation(ProofObligation::assume("b", "budget == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "within_budget == if total_memory <= budget { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fits", "within_budget == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "join memory: 5000+2000=7000 <= 10000 budget");
}
