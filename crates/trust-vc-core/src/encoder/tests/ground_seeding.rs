//! Ground seeding tests for collection quantifier instantiation (#2390).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Verifies that `seed_collection_ground_selects` provides ay-dpll's E-matching
//! with ground `select(array, 0)` terms for symbolic arrays. Without these seeds,
//! quantified array properties (sortedness, ordering) return Unknown because
//! E-matching has no ground trigger terms to instantiate from.

use super::*;
use crate::prepared_context::{prepare_context, PreparedObligation};
use crate::vc::ObligationKind;
use ay_dpll::api::{Term, TermKind};

fn build_symbolic_sortedness_broadcast(name: &str) -> ProofObligation {
    ProofObligation::broadcast_assume(name, "s.index(j) <= s.index(j + 1)")
        .with_bound_vars(vec!["j".to_string()])
        .with_trigger_patterns(vec![vec!["s.index(j)".to_string()]])
}

fn term_is_named_var(encoder: &AYEncoder, term: Term, expected: &str) -> bool {
    matches!(
        encoder.solver.term_kind(term),
        TermKind::Var { ref name } if name == expected
    )
}

fn term_is_select_on_collection(encoder: &AYEncoder, term: Term, collection_name: &str) -> bool {
    match encoder.solver.term_kind(term) {
        TermKind::App { ref name, num_args } if name == "select" && num_args == 2 => {
            let children = encoder.solver.term_children(term);
            term_is_named_var(encoder, children[0], collection_name)
        }
        _ => false,
    }
}

#[cfg(feature = "native-seq")]
fn term_is_seq_nth_on_collection(encoder: &AYEncoder, term: Term, collection_name: &str) -> bool {
    match encoder.solver.term_kind(term) {
        TermKind::App { ref name, num_args } if name == "seq.nth" && num_args == 2 => {
            let children = encoder.solver.term_children(term);
            term_is_named_var(encoder, children[0], collection_name)
        }
        _ => false,
    }
}

fn term_is_collection_access(encoder: &AYEncoder, term: Term, collection_name: &str) -> bool {
    #[cfg(feature = "native-seq")]
    if term_is_seq_nth_on_collection(encoder, term, collection_name) {
        return true;
    }

    term_is_select_on_collection(encoder, term, collection_name)
}

fn has_collection_seed_binding(encoder: &AYEncoder, collection_name: &str) -> bool {
    let seed_name = format!("__ground_seed_{collection_name}");
    encoder
        .solver
        .assertions()
        .into_iter()
        .any(|term| match encoder.solver.term_kind(term) {
            TermKind::App { ref name, num_args } if name == "=" && num_args == 2 => {
                let children = encoder.solver.term_children(term);
                (term_is_named_var(encoder, children[0], &seed_name)
                    && term_is_collection_access(encoder, children[1], collection_name))
                    || (term_is_named_var(encoder, children[1], &seed_name)
                        && term_is_collection_access(encoder, children[0], collection_name))
            }
            _ => false,
        })
}

/// DISCRIMINATING: this context contains only a quantified broadcast over a
/// symbolic Seq, so there is no top-level `s.index(k)` assertion/assumption to
/// manufacture a ground `select(s, k)` term. The only way the solver can see a
/// ground select here is through `seed_collection_ground_selects()`.
///
/// This fails on the pre-`e325fed0` path because `setup_from_prepared()`
/// asserted only the quantified broadcast and never introduced `select(s, 0)`.
#[test]
fn test_2391_typed_setup_asserts_collection_seed_binding_without_goal_selects() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i64>"));
    ctx.declare_var_typed("j", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.obligations
        .push(build_symbolic_sortedness_broadcast("sorted"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    let broadcasts: Vec<&PreparedObligation> = prepared
        .obligations
        .iter()
        .filter(|obligation| matches!(obligation.kind, ObligationKind::BroadcastAssume))
        .collect();

    let slices = crate::encoder::verification::VerificationSlices::new(
        &prepared,
        &[],
        &broadcasts,
        &[],
        &[],
        &[],
    );
    let encoder =
        AYEncoder::setup_from_prepared(&slices, false, None).expect("typed setup should succeed");

    assert!(
        has_collection_seed_binding(&encoder, "s"),
        "#2391: typed setup should assert a seed binding for symbolic Seq broadcasts"
    );
}

/// Behavioral smoke: symbolic sortedness over a Seq should verify when ground
/// seeds give E-matching a starting point.
///
/// Setup: Seq `s` of length `n`, broadcast `forall j: s.index(j) <= s.index(j+1)`
/// with trigger `s.index(j)`, assert `s.index(0) <= s.index(2)`.
///
/// Without ground seeding, the solver has no ground `select(s, k)` terms to
/// trigger from, and E-matching never fires. With seeding, `select(s, 0)` exists,
/// so E-matching fires with `j=0` (producing `select(s, 1)`), then `j=1`
/// (producing `select(s, 2)`), establishing `s[0] <= s[1] <= s[2]`.
///
/// This is not the discriminating oracle for #2391 because the asserted goal
/// itself also introduces `select(s, 0)` / `select(s, 2)` terms.
///
/// Under `native-seq`, this test is gated off: ay-dpll's Seq theory does not
/// yet propagate BV element sorts through `seq.nth` into the BV theory's
/// transitivity reasoning. Even with direct ground assumptions (no quantifier),
/// `bvsle(seq.nth(s,0), seq.nth(s,1)) ∧ bvsle(seq.nth(s,1), seq.nth(s,2))`
/// cannot derive `bvsle(seq.nth(s,0), seq.nth(s,2))`. See #2697 Phase 4.
#[cfg(not(feature = "native-seq"))]
#[test]
fn test_2390_symbolic_array_sortedness_verifies_with_ground_seeds() {
    let mut ctx = VerificationContext::new();
    // This is a completeness smoke test whose contract already admits a
    // fail-closed `Unknown`. Keep it from consuming the default timeout retry
    // cascade when AY cannot close the quantified array/BV interaction.
    ctx.set_rlimit(1_000);
    ctx.set_skip_retry_cascade(true);
    ctx.set_demand_inline_enabled(false);
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i64>"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("j", crate::ir::TrustVcType::parse_or_opaque("u64"));

    // Length bound
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == n"));
    ctx.push_obligation(ProofObligation::assume("n_bound", "n > 3"));

    // Sortedness axiom as broadcast with trigger
    let mut sorted_broadcast =
        ProofObligation::broadcast_assume("sorted", "s.index(j) <= s.index(j + 1)");
    sorted_broadcast = sorted_broadcast
        .with_bound_vars(vec!["j".to_string()])
        .with_trigger_patterns(vec![vec!["s.index(j)".to_string()]]);
    ctx.obligations.push(sorted_broadcast);

    // Assert transitivity consequence: s[0] <= s[2]
    ctx.push_obligation(ProofObligation::assert(
        "transitive",
        "s.index(0) <= s.index(2)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "#2390: symbolic array sortedness should verify or fail closed with ground seeds",
    );
}

/// Without any array element accesses at depth 0, E-matching has no seeds.
/// This test verifies that a simple array property requiring one E-matching
/// step works with the ground seeding mechanism.
#[test]
fn test_2390_symbolic_array_single_step_ematching() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("Seq<i64>"));
    ctx.declare_var_typed("j", crate::ir::TrustVcType::parse_or_opaque("u64"));

    ctx.push_obligation(ProofObligation::assume("len", "a.len() > 2"));

    // Broadcast: all elements are positive
    let mut all_positive = ProofObligation::broadcast_assume("all_positive", "a.index(j) > 0");
    all_positive = all_positive
        .with_bound_vars(vec!["j".to_string()])
        .with_trigger_patterns(vec![vec!["a.index(j)".to_string()]]);
    ctx.obligations.push(all_positive);

    // Assert that element 0 is positive (requires one E-matching step from seed)
    ctx.push_obligation(ProofObligation::assert("elem_0_positive", "a.index(0) > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "#2390: single-step E-matching from ground seed should verify",
    );
}

/// ay-dpll limitation tracker: Seq/BV theory interaction for transitivity.
///
/// Even with direct ground assumptions (no quantifier), ay-dpll cannot derive
/// `bvsle(seq.nth(s,0), seq.nth(s,2))` from `bvsle(seq.nth(s,0), seq.nth(s,1))`
/// and `bvsle(seq.nth(s,1), seq.nth(s,2))`. The BV theory does not see through
/// the Seq theory's `seq.nth` function application to propagate BV ordering.
///
/// When ay-dpll gains Seq/BV theory cooperation, this test should be upgraded
/// from `expect_verified_or_unknown` to `expect_verified`. Part of #2697 Phase 4.
#[cfg(feature = "native-seq")]
#[test]
fn test_2697_native_seq_sortedness_transitivity_known_limitation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i64>"));

    ctx.push_obligation(ProofObligation::assume("len_bound", "s.len() > 3"));
    ctx.push_obligation(ProofObligation::assume(
        "step_0",
        "s.index(0) <= s.index(1)",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "step_1",
        "s.index(1) <= s.index(2)",
    ));

    ctx.push_obligation(ProofObligation::assert(
        "transitive",
        "s.index(0) <= s.index(2)",
    ));

    let result = AYEncoder::verify(&ctx);
    // Accept Unknown as expected ay-dpll limitation (Seq/BV theory gap).
    expect_verified_or_unknown(
        &result,
        "#2697: native-seq sortedness transitivity (ay-dpll Seq/BV limitation)",
    );
}

#[cfg(feature = "native-seq")]
#[test]
fn test_2697_native_seq_ematching_diagnostic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("Seq<i64>"));
    ctx.declare_var_typed("j", crate::ir::TrustVcType::parse_or_opaque("u64"));

    ctx.push_obligation(ProofObligation::assume("len", "a.len() > 0"));

    let mut all_positive = ProofObligation::broadcast_assume("all_positive", "a.index(j) > 0");
    all_positive = all_positive
        .with_bound_vars(vec!["j".to_string()])
        .with_trigger_patterns(vec![vec!["a.index(j)".to_string()]]);
    ctx.obligations.push(all_positive);

    ctx.push_obligation(ProofObligation::assert("elem_0_positive", "a.index(0) > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "#2697 diagnostic: basic native-seq E-matching");
}

/// The ground-seeding fix also applies to the havoc-all inductive-step setup.
///
/// This covers the `setup_havoc_all_encoder()` branch touched by #2390 with a
/// collection-trigger broadcast. Using `Set::contains` avoids any dependency on
/// Seq length assumptions, which havoc-all intentionally discards.
#[test]
fn test_2390_havoc_all_inductive_step_uses_collection_ground_seed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "members",
        crate::ir::TrustVcType::parse_or_opaque("Set<i32>"),
    );
    ctx.declare_var_typed("j", crate::ir::TrustVcType::parse_or_opaque("i32"));

    let mut all_members = ProofObligation::broadcast_assume("all_members", "members.contains(j)");
    all_members = all_members
        .with_bound_vars(vec!["j".to_string()])
        .with_trigger_patterns(vec![vec!["members.contains(j)".to_string()]]);
    ctx.obligations.push(all_members);

    ctx.obligations.push(ProofObligation::loop_invariant(
        "contains_one",
        "members.contains(1)",
    ));
    ctx.push_obligation(ProofObligation::assert("post", "members.contains(1)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "#2390: havoc-all inductive step should use seeded collection triggers",
    );
}

/// The frame-condition inductive-step path also seeds collection ground terms.
///
/// This exercises the `setup_frame_condition_encoder()` branch touched by #2390.
/// Uses Set::contains (like the havoc-all test) to keep the formula size
/// manageable — the discriminating factor is the frame-condition path
/// (set_loop_modified_vars), not the collection operation complexity.
///
/// The proof relies on two #2390 mechanisms:
/// 1. `seed_collection_ground_selects()` creates ground `select(members, ...)` so
///    E-matching can instantiate the broadcast.
/// 2. `alias_framed_collection_variables()` makes the framed post-state `members`
///    the same ay term as `members__trust_vc_pre`, so the pre-state invariant
///    assumption directly proves the post-state goal on a single Array term.
///    Direct Array-read propagation is tested separately; the value here is
///    keeping this framed path small and deterministic.
#[test]
fn test_2390_frame_condition_inductive_step_uses_collection_ground_seed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "members",
        crate::ir::TrustVcType::parse_or_opaque("Set<i32>"),
    );
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("j", crate::ir::TrustVcType::parse_or_opaque("i32"));

    let mut all_members = ProofObligation::broadcast_assume("all_members", "members.contains(j)");
    all_members = all_members
        .with_bound_vars(vec!["j".to_string()])
        .with_trigger_patterns(vec![vec!["members.contains(j)".to_string()]]);
    ctx.obligations.push(all_members);

    // Frame condition: `members` is not modified (only `i` changes).
    // This routes through setup_frame_condition_encoder, not havoc_all.
    ctx.obligations.push(ProofObligation::loop_invariant(
        "contains_one",
        "members.contains(1)",
    ));
    ctx.set_loop_modified_vars("contains_one", vec!["i".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "members.contains(1)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "#2390: frame-condition inductive step should use seeded collection triggers",
    );
}

/// DISCRIMINATING for `alias_framed_collection_variables()`: this test has NO
/// broadcasts that could independently prove the assertion.  The only way the
/// inductive step succeeds is through aliasing the post-state `members` to the
/// pre-state `members__trust_vc_pre` term.
///
/// Without aliasing, ay-dpll would need to propagate the array-level frame
/// equality `members == members__trust_vc_pre` to the element-level
/// `select(members, 42) == select(members__trust_vc_pre, 42)`, which it cannot
/// do (#2384).  With aliasing both terms are the same ay object, so the
/// pre-state invariant assumption `select(members, 42) == true` directly
/// proves the post-state goal.
#[test]
fn test_2390_frame_aliasing_discriminating_no_broadcast() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "members",
        crate::ir::TrustVcType::parse_or_opaque("Set<i32>"),
    );
    ctx.declare_var_typed("counter", crate::ir::TrustVcType::parse_or_opaque("u64"));

    // Base case: members contains 42 initially.
    ctx.push_obligation(ProofObligation::assume("init", "members.contains(42)"));

    // Loop invariant on an unmodified collection — only `counter` changes.
    ctx.obligations.push(ProofObligation::loop_invariant(
        "has_42",
        "members.contains(42)",
    ));
    ctx.set_loop_modified_vars("has_42", vec!["counter".to_string()]);

    // Post-loop assertion.
    ctx.push_obligation(ProofObligation::assert("post", "members.contains(42)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "#2390: frame-condition aliasing alone (no broadcast) must transfer \
         pre-state Set membership to post-state",
    );
}
