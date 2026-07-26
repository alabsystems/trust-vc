// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verus `default_trait.rs` parity for primitive-integer `Default` (cluster
//! #2779, upstream `source/rust_verify_test/tests/default_trait.rs`).
//!
//! Rust's `Default` for every fixed-width primitive integer (and `isize`/`usize`)
//! is definitionally `0`. Upstream Verus encodes the same value: `test_default_ok`
//! checks `<{ty}>::default() == 0` verifies and `test_default_fail` checks
//! `<{ty}>::default() == 1` fails. The macros are parameterized over `{ty}`, and
//! `lower_default_constructor_call` (ir_lowering/dispatch/calls.rs) now lowers all
//! of these to `IntLit { value: 0 }` at the suffix-mapped signedness/width.
//!
//! These end-to-end tests drive the assertion string
//! `syn::parse_str → lower_syn_expr → dispatch → solver`, exercising both
//! directions: `T::default() == 0` must verify, `T::default() == 1` must produce
//! a counterexample (never `Verified`). A fixed `0` is exactly Verus's value, so
//! the feature is equally conservative — sound in both directions.

use super::*;

/// Every primitive-integer `Default` equals `0`: `T::default() == 0` verifies.
/// Mirrors upstream `test_default_*_ok` over all machine-integer widths.
#[test]
fn integer_default_equals_zero_verifies_all_widths() {
    for ty in [
        "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
    ] {
        let mut ctx = VerificationContext::new();
        let condition = format!("{ty}::default() == 0");
        ctx.push_obligation(ProofObligation::assert(
            "default_is_zero",
            condition.clone(),
        ));

        let result = AYEncoder::verify(&ctx);
        expect_verified(
            &result,
            &format!("#2779 default_trait: {condition} must verify (Default is definitionally 0)"),
        );
    }
}

/// The fail direction proves the feature is not unsound: `T::default() == 1` is
/// false for a zero default and must yield a counterexample, never `Verified`.
/// Mirrors upstream `test_default_*_wrong`.
#[test]
fn integer_default_equals_one_is_counterexample_all_widths() {
    for ty in [
        "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
    ] {
        let mut ctx = VerificationContext::new();
        let condition = format!("{ty}::default() == 1");
        ctx.push_obligation(ProofObligation::assert(
            "default_is_one_wrong",
            condition.clone(),
        ));

        let result = AYEncoder::verify(&ctx);
        expect_counterexample(
            &result,
            &format!(
                "#2779 default_trait: {condition} is false for a zero default and must NOT verify"
            ),
        );
    }
}
