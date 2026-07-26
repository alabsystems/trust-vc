// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Seq::count(e)` — number of occurrences of `e` in a sequence.
//!
//! Regression for the overflow-predicate / encode-expression misroute that
//! sent a `Seq` receiver to the `Multiset` count encoder
//! (`encode_multiset_count` → `multiset_element_trust_vc_type`), which rejects
//! a Seq operand with "Expected Multiset<T> operand, got collection kind Seq".
//! `encode_collection_op`'s `Count` arm now routes a `CollectionKind::Seq`
//! receiver to the bounded array-based occurrence count
//! (`encode_seq_occurrence_count`) instead. A `to_multiset()` view is registered
//! as `CollectionKind::Multiset`, so the Multiset path is untouched.
//!
//! These tests exercise the array-based (`Array(BV, T)`) Seq encoding and so are
//! gated off under `native-seq`, where `Seq` uses ay's native `Sort::Seq` and
//! `count` is dispatched to `native_seq_count` by the early `receiver_expr_is_seq`
//! return in `encode_collection_op`.
//!
//! SOUNDNESS: a wrong count is a false-Verified, so both directions are tested.
//! The occurrence-count encoding is sound-or-fail-closed: it is exact for
//! `len < 5` and emits a `len < 5` guard that must be discharged, so an
//! unbounded/over-length sequence cannot verify a count claim (it fails closed
//! to Counterexample/Unknown rather than answering Verified).

#![cfg(not(feature = "native-seq"))]

use super::*;

// A finite Seq literal built from an empty-Seq push chain. `count(e)` is exact
// for these because the length is statically known (< 5).
const SEQ_1_2_1: &str = "trust_vc_types::Seq::<i32>::empty().push(1i32).push(2i32).push(1i32)";

// -----------------------------------------------------------------------------
// (i) TRUE count claims verify.
// -----------------------------------------------------------------------------

#[test]
fn seq_count_literal_two_occurrences_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "count_eq_2",
        &format!("{SEQ_1_2_1}.count(1i32) == 2"),
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seq![1,2,1].count(1) == 2 should verify (1 occurs twice)",
    );
}

#[test]
fn seq_count_empty_is_zero_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "empty_count_zero",
        "trust_vc_types::Seq::<i32>::empty().count(7i32) == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "empty Seq::count(x) == 0 should verify");
}

#[test]
fn seq_count_absent_element_is_zero_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "absent_count_zero",
        &format!("{SEQ_1_2_1}.count(9i32) == 0"),
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seq![1,2,1].count(9) == 0 should verify (9 is absent)",
    );
}

// -----------------------------------------------------------------------------
// (ii) FALSE count claims refute — a wrong count must never verify.
// -----------------------------------------------------------------------------

#[test]
fn seq_count_literal_wrong_value_refutes() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "count_eq_3",
        &format!("{SEQ_1_2_1}.count(1i32) == 3"),
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "seq![1,2,1].count(1) == 3 must refute (the true count is 2)",
    );
}

#[test]
fn seq_count_absent_element_nonzero_refutes() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "absent_count_one",
        &format!("{SEQ_1_2_1}.count(9i32) == 1"),
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "count of an absent element == 1 must refute (the true count is 0)",
    );
}

// -----------------------------------------------------------------------------
// (iii) Symbolic: a provable count fact verifies; a false one fails closed.
// -----------------------------------------------------------------------------

#[test]
fn seq_count_symbolic_provable_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("e0", "s.index(0) == 1"));
    ctx.push_obligation(ProofObligation::assume("e1", "s.index(1) == 2"));
    ctx.push_obligation(ProofObligation::assume("e2", "s.index(2) == 1"));
    ctx.push_obligation(ProofObligation::assert("count_eq_2", "s.count(1) == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "symbolic Seq of [1,2,1]: count(1) == 2 should verify",
    );
}

#[test]
fn seq_count_symbolic_false_does_not_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("e0", "s.index(0) == 1"));
    ctx.push_obligation(ProofObligation::assume("e1", "s.index(1) == 2"));
    ctx.push_obligation(ProofObligation::assume("e2", "s.index(2) == 1"));
    ctx.push_obligation(ProofObligation::assert("count_eq_3", "s.count(1) == 3"));
    let result = AYEncoder::verify(&ctx);
    // Sound fail-closed: a false symbolic count must not verify (Counterexample
    // or Unknown, never Verified).
    expect_not_verified(
        &result,
        "symbolic Seq of [1,2,1]: count(1) == 3 must not verify",
    );
}

// -----------------------------------------------------------------------------
// Fail-closed: an unbounded symbolic Seq cannot verify a count claim — the
// `len < 5` guard is undischargeable, so even the universally-true `count >= 0`
// must fail closed rather than answer Verified.
// -----------------------------------------------------------------------------

#[test]
fn seq_count_unbounded_symbolic_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assert("count_nonneg", "s.count(1) >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "unbounded Seq::count must fail closed (undischargeable len < 5 guard)",
    );
}

// -----------------------------------------------------------------------------
// (iv) Regression guard: Multiset::count(e) is unchanged by the Seq redirect.
// -----------------------------------------------------------------------------

#[test]
fn multiset_count_path_unchanged_after_seq_redirect() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("empty_5", "ms.count(5) == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "count_pos",
        "ms.insert(5).count(5) > 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Multiset::count must still verify after the Seq count redirect",
    );
}

#[test]
fn multiset_count_wrong_value_still_refutes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("empty_5", "ms.count(5) == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "wrong_count",
        "ms.insert(5).count(5) == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Multiset::count(5) == 0 after insert(5) must refute (count is 1)",
    );
}
