//! Collection length tracking (#66), Seq::contains (#1757),
//! Map::contains/contains_key (#1743), and basic membership tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from basic/collections.rs (#2145).

use super::*;

// ========================================================================
// Collection length tracking tests (Part of #66)
// ========================================================================

#[test]
fn test_parse_arr_len_expression() {
    // Test parsing arr.len() == 5 expression (Issue #1191)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("arr", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));

    // Assert arr.len() == 5 to test that the len() expression parses.
    // Changed from add_assume to add_assert after #1859 correctly rejects
    // contexts with only assumptions and no assertions.
    ctx.push_obligation(ProofObligation::assert("arr_len_is_5", "arr.len() == 5"));

    let result = AYEncoder::verify(&ctx);
    // No assumptions constrain arr's length, so NOT(arr.len() == 5) is SAT
    // (solver picks any length != 5). Expect Counterexample (#2229 triage).
    // Under native-seq, ay-dpll's Seq theory disables model validation,
    // so the correct SAT result is demoted to Unknown. Part of #2680.
    #[cfg(feature = "native-seq")]
    expect_fail_closed(
        &result,
        "Unconstrained arr.len() == 5 should produce Counterexample",
    );
    #[cfg(not(feature = "native-seq"))]
    expect_counterexample(
        &result,
        "Unconstrained arr.len() == 5 should produce Counterexample",
    );
}

#[test]
fn test_seq_len_basic() {
    // Test that s.len() returns the tracked length term
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    // Length is always >= 0 by construction
    ctx.push_obligation(ProofObligation::assert("len_nonneg", "s.len() >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Seq.len() >= 0 should verify");
}

#[test]
fn test_seq_is_empty_basic() {
    // Test that is_empty() <=> len() == 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("empty", "s.is_empty()"));
    ctx.push_obligation(ProofObligation::assert("len_zero", "s.len() == 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "is_empty() implies len() == 0");
}

#[test]
fn test_set_len_basic() {
    // Test that Set.len() (cardinality) is tracked
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assert(
        "cardinality_nonneg",
        "s.len() >= 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Set.len() >= 0 should verify");
}

#[test]
fn test_map_len_basic() {
    // Test that Map.len() (cardinality) is tracked
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "cardinality_nonneg",
        "m.len() >= 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Map.len() >= 0 should verify");
}

#[test]
fn test_len_in_comparison() {
    // Test len() in a comparison expression.
    // len() returns unsigned pointer_width (#1745), so use u64 for n.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("n_is_len", "n == s.len()"));
    ctx.push_obligation(ProofObligation::assert("n_nonneg", "n >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "n == s.len() implies n >= 0");
}

#[test]
fn test_non_collection_len_errors() {
    // Non-collection types should error when len() is called
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("invalid", "x.len() >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_error(&result, "len() on non-collection should error");
}

// ========================================================================
// Seq::contains() existential encoding with Int-sorted witness (#1757)
// ========================================================================

#[test]
fn test_seq_contains_encodes_without_error() {
    // Phase 1 validation: encode_seq_contains produces a valid existential
    // formula instead of the old error path. Does not test verification
    // outcome (that depends on s.index() sort coercion — see #2067).
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert("contains_2", "s.contains(2)"));

    let result = AYEncoder::verify(&ctx);
    // Encoding test — ay-dpll may return Unknown for contains (#2229 triage)
    expect_encodes_without_error(&result, "Seq::contains(2)");
}

#[test]
fn test_seq_contains_empty_seq_not_verified() {
    // An empty sequence (len == 0) cannot contain any element.
    // The existential has no valid witness: exists i. 0 <= i < 0 && ... is unsat.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("empty", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert("contains_5", "s.contains(5)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Empty seq containing 5");
}

#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_take_contains_encodes_without_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "take_contains",
        "s.take(3).contains(42)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(
        &result,
        "native-seq chained take(...).contains(...) should encode cleanly",
    );
}

#[test]
fn test_set_contains_still_works() {
    // Set::contains should use select encoding: inserting a different element
    // must not remove existing membership. Requires genuine array theory reasoning.
    // Fixes tautology (#1944): previously assumed s.contains(5) and asserted s.contains(5).
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("has_5", "s.contains(5)"));
    // Insert a different element (10), then assert 5 is still contained.
    // The solver must reason that store(s, 10, true) preserves select(s, 5).
    ctx.push_obligation(ProofObligation::assert(
        "survives_insert",
        "s.insert(10).contains(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Set::contains should survive insert of a different element",
    );
}

// ========================================================================
// Map alias semantics and contains_key/domain coverage (#1743, #2602)
// ========================================================================

#[test]
fn test_map_contains_alias_matches_contains_key() {
    // The TrustWp facade exposes Map::contains() as an alias for contains_key().
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "alias_equiv",
        "m.contains(5) == m.contains_key(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Map::contains() should lower to the same semantics as contains_key()",
    );
}

#[test]
fn test_map_contains_key_recognized() {
    // With domain tracking (#1966), contains_key is now encodable.
    // On a fresh Map, contains_key(5) returns Counterexample (not Error).
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert("has_key", "m.contains_key(5)"));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(&result, "Map::contains_key with domain tracking");
}

#[test]
fn test_map_contains_alias_fresh_map_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert("bad_contains", "m.contains(1)"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "contains alias on a fresh Map should fail closed like contains_key",
    );
}

#[test]
fn test_map_lookup_alias_matches_get() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "lookup_equiv",
        "m.insert(1, true).lookup(1) == m.insert(1, true).get(1)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Map::lookup() should lower to get()");
}

/// Fresh Map: contains_key on a non-inserted key finds counterexample (#1966).
#[test]
fn test_map_contains_key_fresh_map_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "bad_contains_key",
        "m.contains_key(1)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "contains_key on fresh Map should find counterexample",
    );
}

/// Map::dom() returns the domain set — fresh Map's dom should not contain key (#1966).
#[test]
fn test_map_dom_fresh_not_contains() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert("bad_dom", "m.dom().contains(1)"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "Fresh Map dom should not contain arbitrary key");
}

/// When contains() is called on a chained expression (receiver_name = None),
/// it should return an error instead of silently falling through to Set
/// membership semantics. Before the fix, s.view().contains(5) would use
/// try_select(receiver, value) — the Set path — regardless of the actual type.
#[test]
fn test_contains_on_chained_receiver_resolves() {
    // s.view() returns the same term and extract_receiver_name now recurses
    // through MethodCall receivers to find the root variable "s" (#1798).
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("has_5", "s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert("chained", "s.view().contains(5)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s.view().contains(5) should verify when s.contains(5) is assumed (#1798)",
    );
}
