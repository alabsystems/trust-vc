//! Native string theory smoke tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_native_string_literal_contains_verifies_or_unknown() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "literal_contains",
        "\"hello\".contains(\"ell\")",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "native string literal contains should not fail closed",
    );
}

#[test]
fn test_native_string_literal_starts_with_verifies_or_unknown() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "literal_starts_with",
        "\"hello\".starts_with(\"he\")",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "native string literal starts_with should not fail closed",
    );
}

#[test]
fn test_native_string_literal_ends_with_verifies_or_unknown() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "literal_ends_with",
        "\"hello\".ends_with(\"lo\")",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "native string literal ends_with should not fail closed",
    );
}

#[test]
fn test_native_string_symbolic_len_is_nonnegative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::String);
    ctx.push_obligation(ProofObligation::assert("len_nonnegative", "s.len() >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "native string len should stay non-negative");
}

#[test]
fn test_native_string_view_len_matches_direct_len() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::String);
    ctx.push_obligation(ProofObligation::assert(
        "view_bridge",
        "s.view().len() == s.len()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "native string view() should bridge to the direct native string length",
    );
}

#[test]
fn test_native_string_ext_eq_matches_explicit_view_formula() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lhs", crate::ir::TrustVcType::String);
    ctx.declare_var_typed("rhs", crate::ir::TrustVcType::String);
    ctx.push_obligation(ProofObligation::assert(
        "ext_eq_bridge",
        "ext_eq!(lhs, rhs) == ext_eq!(lhs.view(), rhs.view())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "native string ext_eq! should lower through the same Seq<char> bridge as explicit views",
    );
}

#[test]
fn test_native_string_literal_view_supports_index() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "literal_view_index",
        "\"hi\".view().index(0) == 'h'",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "native string view bridge should support literal char indexing",
    );
}
