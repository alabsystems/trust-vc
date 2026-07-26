// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ToSet/ToMultiset are not yet implemented under native-seq encoding.
// These tests exercise the array-based projection-view approach which
// doesn't apply when Seq uses ay's native Sort::Seq. Part of #2680.
#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_to_set_contains_inserted_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "to_set_contains",
        "s.to_set().contains(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    // index 0 is in range (len == 2) and holds 5, so 5 is a member of the
    // element set s.to_set(). The derived Set-view grounds membership as the
    // disjunction `∃ i in [0,len): s[i] == v`, which proves this soundly.
    expect_verified(
        &result,
        "Seq::to_set().contains(v) should verify when an in-range index holds v",
    );
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_to_set_contains_fifth_element_at_len_five() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assume("elem4", "s.index(4) == 13"));
    ctx.push_obligation(ProofObligation::assert(
        "to_set_contains_fifth",
        "s.to_set().contains(13)",
    ));

    let result = AYEncoder::verify(&ctx);
    // index 4 is in range (len == 5) and holds 13, so 13 is a member of the
    // element set s.to_set(). Membership grounds to `∃ i in [0,len): s[i] == v`,
    // proving this soundly at the bounded unroll limit.
    expect_verified(
        &result,
        "Seq::to_set().contains(v) should verify when an in-range index holds v",
    );
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_to_set_finite_verifies_for_unbounded_source_element_domain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<nat>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert("finite", "s.to_set().finite()"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::to_set().finite() should verify from finite sequence provenance",
    );
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_constructed_seq_to_set_contains_pushed_element() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "constructed_to_set_contains",
        "trust_vc_types::Seq::<i32>::empty().push(5i32).push(8i32).to_set().contains(5i32)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "constructed Seq::to_set() should contain a pushed element",
    );
}

#[test]
fn test_seq_push_index_reads_last_pushed_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "last_pushed",
        "s.push(99i32).index(2usize) == 99i32",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::push(v).index(old_len) should read the last pushed element",
    );
}

#[test]
fn test_seq_push_index_rejects_wrong_last_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "wrong_last_pushed",
        "s.push(99i32).index(2usize) == 100i32",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Seq::push(v).index(old_len) must not verify a wrong pushed value",
    );
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_to_set_rejects_element_proved_absent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("absent", "!s.contains(9)"));
    ctx.push_obligation(ProofObligation::assert(
        "to_set_contains_absent",
        "s.to_set().contains(9)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "s.to_set() must not contain an element proved absent from the source",
    );
}

#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_to_set_contains_matches_source_contains() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("source_has_5", "s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "to_set_has_5",
        "s.to_set().contains(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "native Seq::to_set().contains(e) should follow Seq::contains(e)",
    );
}

#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_to_set_rejects_element_proved_absent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("source_not_9", "!s.contains(9)"));
    ctx.push_obligation(ProofObligation::assert(
        "to_set_has_9",
        "s.to_set().contains(9)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "native Seq::to_set() must not contain an element absent from the source",
    );
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_to_set_insert_returns_projection_view_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assert(
        "unsupported_insert",
        "s.to_set().insert(9).contains(9)",
    ));

    let result = AYEncoder::verify(&ctx);
    match &result {
        crate::encoder::VerifyResult::Error { message } => {
            assert!(
                message.contains("Seq::to_set() projection views currently support contains() and finite() only"),
                "derived Set-view error should mention the supported-only projection contract, got: {message}",
            );
        }
        other => panic!(
            "Seq::to_set().insert(...) must fail closed with an encoder error, got: {:?}",
            other
        ),
    }
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_to_multiset_counts_duplicates() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 5"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "dup_count",
        "s.to_multiset().count(5) == 2u64",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s.to_multiset().count(5) should equal the number of duplicate occurrences",
    );
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_to_multiset_contains_inserted_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 5"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "contains",
        "s.to_multiset().contains(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Seq::to_multiset() should contain an element that occurs in the source sequence",
    );
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_to_multiset_insert_returns_projection_view_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assert(
        "unsupported_insert",
        "s.to_multiset().insert(9).contains(9)",
    ));

    let result = AYEncoder::verify(&ctx);
    match &result {
        crate::encoder::VerifyResult::Error { message } => {
            assert!(
                message.contains(
                    "Seq::to_multiset() projection views currently support contains() and count() only",
                ),
                "derived Multiset-view error should mention the supported-only projection contract, got: {message}",
            );
        }
        other => panic!(
            "Seq::to_multiset().insert(...) must fail closed with an encoder error, got: {:?}",
            other
        ),
    }
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_to_multiset_count_requires_bounded_len() {
    let mut ctx = VerificationContext::new();
    // Multiset count on len=5 seq times out. skip_retry_cascade +
    // demand-inline disabled to avoid wasting time on retry paths.
    ctx.set_rlimit(5_000);
    ctx.set_skip_retry_cascade(true);
    ctx.set_demand_inline_enabled(false);
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "unbounded_count",
        "s.to_multiset().count(5) == 0u64",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Seq::to_multiset().count() must stay fail-closed once len >= 5",
    );
}

#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_to_multiset_rejects_wrong_count() {
    let mut ctx = VerificationContext::new();
    // Wrong-count rejection times out. skip_retry_cascade + demand-inline
    // disabled to avoid wasting time on retry paths.
    ctx.set_rlimit(5_000);
    ctx.set_skip_retry_cascade(true);
    ctx.set_demand_inline_enabled(false);
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 5"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "wrong_count",
        "s.to_multiset().count(5) == 1u64",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "to_multiset().count(5) must NOT be 1 when 5 appears twice",
    );
}

#[test]
fn test_seq_add_concat_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len1", "s1.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("len2", "s2.len() == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "concat_len",
        "s1.add(s2).len() == 5",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s1.add(s2).len() should be 5 when lens are 2+3");
}

#[test]
fn test_seq_add_rejects_push_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len1", "s1.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("len2", "s2.len() == 3"));
    ctx.push_obligation(ProofObligation::assert("push_len", "s1.add(s2).len() == 3"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "s1.add(s2).len() == 3 when s2.len() == 3");
}

#[test]
fn test_seq_add_preserves_lhs() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len1", "s1.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("len2", "s2.len() == 1"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s1.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "preserved",
        "s1.add(s2).index(0) == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s1.add(s2) should preserve s1[0]==10");
}

#[test]
fn test_seq_add_wrong_head_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len1", "s1.len() == 1"));
    ctx.push_obligation(ProofObligation::assume("len2", "s2.len() == 1"));
    ctx.push_obligation(ProofObligation::assume("left_head", "s1.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assume("right_head", "s2.index(0) == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "wrong_head",
        "s1.add(s2).index(0) == s2.index(0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "#2796: direct concat indexing must not verify wrong-head equality",
    );
}
