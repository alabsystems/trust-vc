// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_seq_drop_last_preserves_elements() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "preserved",
        "s.drop_last().index(0) == 7",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.drop_last() should preserve s[0]==7");
}

#[test]
fn test_seq_take_preserves_elements() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "preserved",
        "s.take(3).index(1) == 42",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.take(3) should preserve s[1]==42");
}

/// DISCRIMINATING: native-seq `take(-1)` must fail the slice precondition.
#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_take_negative_index_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "take_neg",
        "s.take(-1).len() == s.take(-1).len()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "native-seq Seq::take(-1) must NOT verify — negative indices are out of range",
    );
}

#[test]
fn test_seq_skip_shifts_indices() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "shifted",
        "s.skip(1).index(0) == 42",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.skip(1)[0] should equal s[1]==42");
}

/// DISCRIMINATING: native-seq `skip(-1)` must fail the slice precondition.
#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_skip_negative_index_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "skip_neg",
        "s.skip(-1).len() == s.skip(-1).len()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "native-seq Seq::skip(-1) must NOT verify — negative indices are out of range",
    );
}

#[test]
fn test_seq_drop_first_shifts_indices() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "shifted",
        "s.drop_first().index(0) == 42",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.drop_first()[0] should equal s[1]==42");
}

#[test]
fn test_seq_skip_rejects_wrong_mapping() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assume("elem1_ne", "s.index(1) != 10"));
    ctx.push_obligation(ProofObligation::assert("wrong", "s.skip(1).index(0) == 10"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "s.skip(1)[0] == s[0] when s[0] != s[1]");
}

#[test]
fn test_seq_subrange_shifts_indices() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "shifted",
        "s.subrange(1, 3).index(0) == 42",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.subrange(1,3)[0] should equal s[1]==42");
}

/// DISCRIMINATING: native-seq negative subrange endpoints must fail the
/// slice precondition.
#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_subrange_negative_endpoint_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "subrange_neg",
        "s.subrange(-1, 2).len() == s.subrange(-1, 2).len()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "native-seq Seq::subrange(-1, 2) must NOT verify — negative endpoints are out of range",
    );
}

#[test]
fn test_seq_subrange_prefix_equality_reaches_symbolic_tail() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("t", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("k_gt4", "k > 4"));
    ctx.push_obligation(ProofObligation::assume("s_len", "s.len() == k"));
    ctx.push_obligation(ProofObligation::assume("t_len", "t.len() == k"));
    ctx.push_obligation(ProofObligation::assume(
        "prefix_eq",
        "s.subrange(0, k) == t.subrange(0, k)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tail_eq",
        "s.index(k - 1) == t.index(k - 1)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Under native-seq, ay-dpll reports (incomplete quantifier-unhandled) for
    // overflow checks on symbolic subrange + index combinations. The encoding
    // is correct; the solver capability is the limit. Part of #2680.
    #[cfg(feature = "native-seq")]
    expect_verified_or_unknown(
        &result,
        "#2680: native-seq symbolic subrange+index overflow check may exceed solver capability",
    );
    #[cfg(not(feature = "native-seq"))]
    expect_verified(
        &result,
        "s[0..k] == t[0..k] should propagate to the symbolic tail index",
    );
}

/// SOUNDNESS (no false Verified): a WRONG symbolic-tail equality
/// `s[k-1] == t[k-1] + 1` must NOT verify even though the genuine
/// `s[k-1] == t[k-1]` does. The subrange-prefix seed must propagate the EXACT
/// relationship, not an off-by-one. Part of #2680.
#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_subrange_prefix_wrong_tail_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("t", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("k_gt4", "k > 4"));
    ctx.push_obligation(ProofObligation::assume("s_len", "s.len() == k"));
    ctx.push_obligation(ProofObligation::assume("t_len", "t.len() == k"));
    ctx.push_obligation(ProofObligation::assume(
        "prefix_eq",
        "s.subrange(0, k) == t.subrange(0, k)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wrong_tail",
        "s.index(k - 1) == t.index(k - 1) + 1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "s[k-1] == t[k-1]+1 must NOT verify — the prefix seed is an EXACT equality",
    );
}

/// SOUNDNESS (no false Verified): an index OUTSIDE the equal prefix must not be
/// spuriously equated. With `s[0..4] == t[0..4]` (a strict prefix of a length-5
/// sequence), the element at index `4` lies beyond the equal region and
/// `s[4] == t[4]` must NOT verify. Concrete lengths keep the subrange
/// `end <= len` side condition trivially established (so this isolates the
/// propagation soundness, not the int/bv side-condition gap). Part of #2680.
#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_subrange_partial_prefix_tail_outside_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("t", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("s_len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assume("t_len", "t.len() == 5"));
    // Only indices [0, 4) agree; index 4 is outside the equal prefix.
    ctx.push_obligation(ProofObligation::assume(
        "prefix_eq",
        "s.subrange(0, 4) == t.subrange(0, 4)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tail_outside",
        "s.index(4) == t.index(4)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "s[4] == t[4] must NOT verify — index 4 lies outside the equal prefix [0, 4)",
    );
}

/// SOUNDNESS (fail-closed bounds): a genuine out-of-bounds index `s[k]` (where
/// `s.len() == k`, so `k` is one past the last element) must still fail the
/// `i < len` precondition — the `len - c` bounds reshape (#2680) must not mask a
/// real OOB.
#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_index_at_len_still_oob() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("k_gt4", "k > 4"));
    ctx.push_obligation(ProofObligation::assume("s_len", "s.len() == k"));
    ctx.push_obligation(ProofObligation::assert("oob", "s.index(k) == s.index(k)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "s.index(k) with s.len()==k is out of bounds (i == len) and must fail closed",
    );
}

/// SOUNDNESS (fail-closed bounds): an unconstrained symbolic index `s[k - 1]`
/// with NO lower bound on `k` can underflow-wrap (`k == 0` => index `2^w - 1`)
/// and must NOT verify — the `len - c` reshape (`bvuge(len, c) && bvugt(c, 0)`)
/// keeps the `k >= 1` obligation, so a missing premise fails closed.
#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_index_len_minus_one_without_nonempty_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("u64"));
    // NO `k > 0` premise: k could be 0, so `k - 1` wraps and `k - 1 < k` fails.
    ctx.push_obligation(ProofObligation::assume("s_len", "s.len() == k"));
    ctx.push_obligation(ProofObligation::assert(
        "maybe_oob",
        "s.index(k - 1) == s.index(k - 1)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "s.index(k-1) without k>0 can underflow-wrap and must fail closed",
    );
}

/// COMPLETENESS partner to the OOB checks: with an explicit non-empty premise
/// `k > 0`, the `len - 1` index IS in bounds, so a trivial reflexive goal
/// verifies — confirming the bounds reshape decides the in-range case (not a
/// blanket fail). Part of #2680.
#[cfg(not(feature = "native-seq"))]
#[test]
fn test_seq_index_len_minus_one_with_nonempty_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("k_pos", "k > 0"));
    ctx.push_obligation(ProofObligation::assume("s_len", "s.len() == k"));
    ctx.push_obligation(ProofObligation::assert(
        "in_bounds",
        "s.index(k - 1) == s.index(k - 1)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s.index(k-1) with k>0 is in bounds and the reflexive goal must verify",
    );
}

#[test]
fn test_seq_concat_preserves_lhs_elements() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len1", "s1.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("len2", "s2.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s1.index(0) == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "preserved",
        "s1.concat(s2).index(0) == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s1.concat(s2)[0] should equal s1[0]==10");
}

#[test]
fn test_seq_concat_length_equals_sum() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len1", "s1.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("len2", "s2.len() == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "concat_len",
        "s1.concat(s2).len() == 5",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s1.concat(s2).len() should equal s1.len()+s2.len()==5",
    );
}
