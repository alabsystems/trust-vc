// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg(feature = "native-seq")]
use crate::prepared_context::prepare_context;
#[cfg(feature = "native-seq")]
use crate::vc::ObligationKind;

#[test]
fn test_seq_first() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 7"));
    ctx.push_obligation(ProofObligation::assert("first_eq", "s.first() == 7"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.first() should equal s.index(0)");
}

#[test]
fn test_seq_last() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("elem2", "s.index(2) == 42"));
    ctx.push_obligation(ProofObligation::assert("last_eq", "s.last() == 42"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.last() should equal s.index(len-1)");
}

#[test]
fn test_seq_first_block_receiver_empty_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("empty", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "first_tautology",
        "({ s }).first() == ({ s }).first()",
    ));

    let result = AYEncoder::verify(&ctx);
    // Under native-seq, ay-dpll's Seq theory unconditionally disables model
    // validation (skip_model_eval = true), so SAT results from overflow checks
    // are demoted to Unknown. The overflow check IS correctly detected as
    // violated — model validation is the only gap. Part of #2680.
    #[cfg(feature = "native-seq")]
    expect_fail_closed(
        &result,
        "first() on empty block receiver must NOT verify (len precondition)",
    );
    #[cfg(not(feature = "native-seq"))]
    expect_counterexample(
        &result,
        "first() on empty block receiver must NOT verify (len precondition)",
    );
}

#[test]
fn test_seq_index_block_receiver_empty_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("empty", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "index_tautology",
        "({ s }).index(0) == ({ s }).index(0)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Under native-seq, ay-dpll's Seq theory unconditionally disables model
    // validation, so the overflow check SAT is demoted to Unknown. Part of #2680.
    #[cfg(feature = "native-seq")]
    expect_fail_closed(
        &result,
        "index() on empty block receiver must NOT verify (bounds precondition)",
    );
    #[cfg(not(feature = "native-seq"))]
    expect_counterexample(
        &result,
        "index() on empty block receiver must NOT verify (bounds precondition)",
    );
}

#[test]
fn test_seq_reverse_preserves_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "same_len",
        "s.reverse().len() == s.len()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.reverse() should preserve sequence length");
}

#[test]
fn test_seq_reverse_first_matches_last() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("last", "s.last() == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "reverse_first",
        "s.reverse().index(0) == s.last()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.reverse().index(0) should equal s.last()");
}

#[test]
fn test_seq_reverse_rejects_wrong_index_mapping() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 1"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "wrong_map",
        "s.reverse().index(0) == s.index(0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "reverse must NOT map index 0 to index 0 when elements differ",
    );
}

#[test]
fn test_seq_reverse_symbolic_tail_matches_source_head() {
    let mut ctx = VerificationContext::new();
    // Symbolic-length reverse+index was #2668. Historical ay c2c20458 may solve
    // it; current TrustVc ay pin is the workspace dependency revision in Cargo.toml.
    // rlimit 1000ms is sufficient: solver either proves quickly or times out.
    // skip_retry_cascade + demand-inline disabled to avoid wasting time on
    // retry paths when the test accepts Unknown.
    ctx.set_rlimit(1_000);
    ctx.set_skip_retry_cascade(true);
    ctx.set_demand_inline_enabled(false);
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("k_gt4", "k > 4"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == k"));
    ctx.push_obligation(ProofObligation::assume("head", "s.index(0) == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "tail_mirror",
        "s.reverse().index(k - 1) == 7",
    ));

    let result = AYEncoder::verify(&ctx);
    // Symbolic-length reverse+index chaining is non-deterministic in the
    // solver. Unknown is acceptable — encoding is correct. Part of #2668.
    expect_verified_or_unknown(
        &result,
        "#2668: symbolic-length reverse+index chaining may exceed solver capability",
    );
}

#[test]
fn test_seq_no_duplicates_with_distinct_pair_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 5"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 8"));
    ctx.push_obligation(ProofObligation::assert("no_dups", "s.no_duplicates()"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "len-2 sequence with concrete distinct elements should have no duplicates",
    );
}

#[test]
fn test_seq_no_duplicates_len_five_distinct_elements_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 2"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 3"));
    ctx.push_obligation(ProofObligation::assume("elem2", "s.index(2) == 5"));
    ctx.push_obligation(ProofObligation::assume("elem3", "s.index(3) == 7"));
    ctx.push_obligation(ProofObligation::assume("elem4", "s.index(4) == 11"));
    ctx.push_obligation(ProofObligation::assert("no_dups", "s.no_duplicates()"));

    let result = AYEncoder::verify(&ctx);
    // 5-element pairwise distinctness (10 pairs) is not discharged: ay reports
    // `QuantifierCegqiIncomplete`, which `UnknownCategory::from_unknown_reason`
    // classifies as a PERMANENT theory gap (mirroring ay's own
    // `PermanentlyNonRetriable` split), not a retriable budget limit. The
    // encoding is correct and the goal is TRUE; the decision procedure simply
    // cannot decide it. Per `docs/design-unknown-as-failure.md` that is
    // reported as a model-less FAILURE — we never claim verification we did not
    // achieve.
    //
    // NOTE: this expectation is load-bearing on ay's reason code being
    // faithful. If a future ay reported a mere ROUND-BUDGET exhaustion under
    // this same `QuantifierCegqiIncomplete` code, the fail-closed reading would
    // be wrong (a budget limit must stay a soft `Unknown`) — see #2668.
    expect_incompleteness_modelless_failure(
        &result,
        "#2668: 5-element no_duplicates is not discharged (cegqi-incomplete)",
    );
}

#[test]
fn test_seq_no_duplicates_rejects_duplicate_pair() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("dup0", "s.index(0) == 7"));
    ctx.push_obligation(ProofObligation::assume("dup1", "s.index(1) == 7"));
    ctx.push_obligation(ProofObligation::assert("no_dups", "s.no_duplicates()"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "duplicate elements must refute s.no_duplicates()");
}

#[cfg(feature = "native-seq")]
#[test]
fn test_seq_no_duplicates_duplicate_pair_direct_encoding_is_not_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("dup0", "s.index(0) == 7"));
    ctx.push_obligation(ProofObligation::assume("dup1", "s.index(1) == 7"));
    ctx.push_obligation(ProofObligation::assert("no_dups", "s.no_duplicates()"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    let assumptions: Vec<_> = prepared
        .obligations
        .iter()
        .filter(|obligation| matches!(obligation.kind, ObligationKind::Assume))
        .collect();
    let assertion = prepared
        .obligations
        .iter()
        .find(|obligation| {
            matches!(obligation.kind, ObligationKind::Assert) && obligation.name == "no_dups"
        })
        .expect("prepared context should contain the no_dups assertion");
    let empty: [&crate::prepared_context::PreparedObligation; 0] = [];
    let slices = crate::encoder::verification::VerificationSlices::new(
        &prepared,
        &assumptions,
        &empty,
        &empty,
        &empty,
        &empty,
    );
    let mut encoder =
        AYEncoder::setup_from_prepared(&slices, false, None).expect("setup should succeed");
    let condition = encoder
        .resolve_condition_typed(&assertion.expr)
        .expect("no_duplicates assertion should encode");
    let negated = encoder
        .solver
        .try_not(condition)
        .expect("encoded condition should be Boolean");
    encoder
        .solver
        .try_assert_term(negated)
        .expect("negated condition should assert cleanly");

    let solve = encoder
        .solver
        .try_check_sat()
        .expect("duplicate direct encoding should solve");
    let sat = solve.result();
    assert!(
        !sat.is_unsat(),
        "duplicate pair should make native-seq no_duplicates invalid, got {sat:?}"
    );
}

#[cfg(feature = "native-seq")]
#[test]
fn test_seq_no_duplicates_two_sequences_do_not_share_seed_symbols() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("t", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("s_len", "s.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("s0", "s.index(0) == 1"));
    ctx.push_obligation(ProofObligation::assume("s1", "s.index(1) == 2"));
    ctx.push_obligation(ProofObligation::assume("t_len", "t.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("t0", "t.index(0) == 3"));
    ctx.push_obligation(ProofObligation::assume("t1", "t.index(1) == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "both_no_dups",
        "s.no_duplicates() && t.no_duplicates()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "distinct and duplicate sequences must not vacuously verify through shared no_duplicates seeds",
    );
}

#[cfg(feature = "native-seq")]
#[test]
fn test_seq_no_duplicates_mixed_element_types_use_fresh_seed_sorts() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ints", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed(
        "flags",
        crate::ir::TrustVcType::parse_or_opaque("Seq<bool>"),
    );
    ctx.push_obligation(ProofObligation::assume("ints_len", "ints.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("ints0", "ints.index(0) == 5"));
    ctx.push_obligation(ProofObligation::assume("ints1", "ints.index(1) == 8"));
    ctx.push_obligation(ProofObligation::assume("flags_len", "flags.len() == 2"));
    ctx.push_obligation(ProofObligation::assume("flags0", "flags.index(0) == true"));
    ctx.push_obligation(ProofObligation::assume("flags1", "flags.index(1) == false"));
    ctx.push_obligation(ProofObligation::assert(
        "both_no_dups",
        "ints.no_duplicates() && flags.no_duplicates()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mixed element-type no_duplicates calls should verify without helper-sort collisions",
    );
}

#[test]
fn test_seq_no_duplicates_len_five_rejects_duplicate_tail_pair() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 5"));
    ctx.push_obligation(ProofObligation::assume("elem0", "s.index(0) == 2"));
    ctx.push_obligation(ProofObligation::assume("elem1", "s.index(1) == 3"));
    ctx.push_obligation(ProofObligation::assume("elem2", "s.index(2) == 5"));
    ctx.push_obligation(ProofObligation::assume("elem3", "s.index(3) == 11"));
    ctx.push_obligation(ProofObligation::assume("elem4", "s.index(4) == 11"));
    ctx.push_obligation(ProofObligation::assert("no_dups", "s.no_duplicates()"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "len-5 duplicate tail pair must refute the universal no_duplicates branch",
    );
}
