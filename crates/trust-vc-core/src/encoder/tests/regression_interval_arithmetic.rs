// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn point_in_interval() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "point_in_interval",
        "x >= lo && x <= hi",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "point should lie within the closed interval");
}

#[test]
fn interval_subset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("lo1", i32_ty());
    ctx.declare_var_typed("hi1", i32_ty());
    ctx.declare_var_typed("lo2", i32_ty());
    ctx.declare_var_typed("hi2", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo1_val", "lo1 == 2"));
    ctx.push_obligation(ProofObligation::assume("hi1_val", "hi1 == 8"));
    ctx.push_obligation(ProofObligation::assume("lo2_val", "lo2 == 0"));
    ctx.push_obligation(ProofObligation::assume("hi2_val", "hi2 == 10"));
    ctx.push_obligation(ProofObligation::assume("in_subset", "x >= lo1 && x <= hi1"));
    ctx.push_obligation(ProofObligation::assert(
        "interval_subset",
        "x >= lo2 && x <= hi2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "subset interval membership should lift to the superset",
    );
}

#[test]
fn interval_midpoint() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.declare_var_typed("mid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume("mid_val", "mid == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "interval_midpoint",
        "mid >= lo && mid <= hi",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "midpoint should lie within the interval");
}

#[test]
fn interval_width() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 3"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 7"));
    ctx.push_obligation(ProofObligation::assert("interval_width", "hi - lo == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "interval width should match the difference of bounds",
    );
}

#[test]
fn interval_nonempty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assert("interval_nonempty", "hi >= lo"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "upper bound should be at least the lower bound");
}

#[test]
fn interval_contains_endpoint() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 5"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 15"));
    ctx.push_obligation(ProofObligation::assert(
        "interval_contains_endpoint",
        "lo >= lo && lo <= hi",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lower endpoint should be contained in the interval",
    );
}

#[test]
fn interval_shift() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.declare_var_typed("offset", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 10"));
    ctx.push_obligation(ProofObligation::assume("offset_val", "offset == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "interval_shift",
        "x + offset >= lo + offset && x + offset <= hi + offset",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shifting an interval should preserve containment");
}

#[test]
fn disjoint_intervals() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("left_interval", "x >= 0 && x <= 5"));
    ctx.push_obligation(ProofObligation::assert(
        "disjoint_intervals",
        "!(x >= 10 && x <= 20)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "a point in one interval should not lie in a disjoint interval",
    );
}

#[test]
fn interval_intersection_nonempty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("lo1", i32_ty());
    ctx.declare_var_typed("hi1", i32_ty());
    ctx.declare_var_typed("lo2", i32_ty());
    ctx.declare_var_typed("hi2", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo1_val", "lo1 == 0"));
    ctx.push_obligation(ProofObligation::assume("hi1_val", "hi1 == 10"));
    ctx.push_obligation(ProofObligation::assume("lo2_val", "lo2 == 5"));
    ctx.push_obligation(ProofObligation::assume("hi2_val", "hi2 == 15"));
    ctx.push_obligation(ProofObligation::assume("in_overlap", "x >= 5 && x <= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "interval_intersection_nonempty",
        "x >= lo1 && x <= hi1 && x >= lo2 && x <= hi2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "a point in the overlap should satisfy both intervals",
    );
}

#[test]
fn interval_split() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("mid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("interval", "x >= 0 && x <= 20"));
    ctx.push_obligation(ProofObligation::assume("mid_val", "mid == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "interval_split",
        "(x <= mid) || (x > mid)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "every point should fall on one side of the split");
}
