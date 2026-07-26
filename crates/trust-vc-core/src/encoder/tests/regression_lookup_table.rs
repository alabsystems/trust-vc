// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn direct_lookup() {
    let mut ctx = VerificationContext::new();
    for v in &["idx", "val"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("idx_val", "idx == 2"));
    // Table: [10, 20, 30, 40, 50]
    ctx.push_obligation(ProofObligation::assume(
        "val_def",
        "val == if idx == 0 { 10 } else { if idx == 1 { 20 } else { if idx == 2 { 30 } else { if idx == 3 { 40 } else { 50 } } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("found", "val == 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "table[2] = 30");
}

#[test]
fn lookup_first() {
    let mut ctx = VerificationContext::new();
    for v in &["idx", "val"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("idx_val", "idx == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "val_def",
        "val == if idx == 0 { 100 } else { if idx == 1 { 200 } else { 300 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("first", "val == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "table[0] = 100");
}

#[test]
fn lookup_last() {
    let mut ctx = VerificationContext::new();
    for v in &["idx", "val"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("idx_val", "idx == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "val_def",
        "val == if idx == 0 { 100 } else { if idx == 1 { 200 } else { 300 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("last", "val == 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "table[2] = 300");
}

#[test]
fn bounded_index() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("idx", u32_ty());
    ctx.declare_var_typed("len", u32_ty());
    ctx.push_obligation(ProofObligation::assume("idx_val", "idx == 3"));
    ctx.push_obligation(ProofObligation::assume("len_val", "len == 5"));
    ctx.push_obligation(ProofObligation::assert("in_bounds", "idx < len"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 < 5 (index in bounds)");
}

#[test]
fn linear_interpolation() {
    let mut ctx = VerificationContext::new();
    for v in &["x0", "y0", "x1", "y1", "x", "y"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    // Linear interpolation between (0, 0) and (10, 100) at x=5 → y=50
    ctx.push_obligation(ProofObligation::assume("x0_val", "x0 == 0"));
    ctx.push_obligation(ProofObligation::assume("y0_val", "y0 == 0"));
    ctx.push_obligation(ProofObligation::assume("x1_val", "x1 == 10"));
    ctx.push_obligation(ProofObligation::assume("y1_val", "y1 == 100"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    // y = y0 + (y1-y0)*(x-x0)/(x1-x0) = 0 + 100*5/10 = 50
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == y0 + (y1 - y0) * (x - x0) / (x1 - x0)",
    ));
    ctx.push_obligation(ProofObligation::assert("interpolated", "y == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "lerp(0,0,10,100,5) = 50");
}

#[test]
fn binary_search_midpoint() {
    let mut ctx = VerificationContext::new();
    for v in &["lo", "hi", "mid"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 2"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "mid_def",
        "mid == lo + (hi - lo) / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("mid_val", "mid == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "midpoint(2, 8) = 5");
}

#[test]
fn step_function_lookup() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "result"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 15"));
    // Step function: x<10 → 0, x<20 → 1, x<30 → 2, else → 3
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if x < 10 { 0 } else { if x < 20 { 1 } else { if x < 30 { 2 } else { 3 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("step", "result == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "step(15) = 1 (in [10,20) range)");
}

#[test]
fn reverse_lookup() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "idx"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Given value, find index in table [10, 20, 30]
    ctx.push_obligation(ProofObligation::assume("val_val", "val == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "idx_def",
        "idx == if val == 10 { 0 } else { if val == 20 { 1 } else { 2 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("found_idx", "idx == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reverse lookup: value 20 -> index 1");
}

#[test]
fn default_on_miss() {
    let mut ctx = VerificationContext::new();
    for v in &["key", "val"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Table has keys 1,2,3 with values 10,20,30; default = 0
    ctx.push_obligation(ProofObligation::assume("key_val", "key == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "val_def",
        "val == if key == 1 { 10 } else { if key == 2 { 20 } else { if key == 3 { 30 } else { 0 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("default", "val == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "key=5 not in table, returns default 0");
}

#[test]
fn table_monotone() {
    // Verify that table values are monotonically increasing
    let mut ctx = VerificationContext::new();
    for v in &["v0", "v1", "v2", "v3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v0_val", "v0 == 10"));
    ctx.push_obligation(ProofObligation::assume("v1_val", "v1 == 25"));
    ctx.push_obligation(ProofObligation::assume("v2_val", "v2 == 30"));
    ctx.push_obligation(ProofObligation::assume("v3_val", "v3 == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "monotone",
        "v0 < v1 && v1 < v2 && v2 < v3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "table [10,25,30,42] is strictly increasing");
}
