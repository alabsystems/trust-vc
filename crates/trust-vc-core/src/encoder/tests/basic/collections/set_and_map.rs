//! Set insert/remove, set operations (union, intersect, difference,
//! subset, superset), Map insert, Map domain tracking (#1966),
//! and Map::dom().len().
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from basic/collections.rs (#2145).

use super::*;

// ========================================================================
// Set::insert() and Set::remove() (Part of #1748)
// ========================================================================

#[test]
fn test_set_insert() {
    // s.insert(5).contains(5) should be true
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assert(
        "inserted",
        "s.insert(5).contains(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.insert(5).contains(5) should verify");
}

#[test]
fn test_set_insert_preserves_existing() {
    // If s.contains(3), then s.insert(5).contains(3) should still be true.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("has_3", "s.contains(3)"));
    ctx.push_obligation(ProofObligation::assert(
        "still_has_3",
        "s.insert(5).contains(3)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.insert(5) should preserve s.contains(3)");
}

#[test]
fn test_set_remove() {
    // s.remove(5).contains(5) should be false
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    // Require non-empty set to satisfy remove overflow checks (#2154)
    ctx.push_obligation(ProofObligation::assume("len_pos", "s.len() > 0"));
    ctx.push_obligation(ProofObligation::assume("has_5", "s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "removed",
        "!s.remove(5).contains(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.remove(5).contains(5) should be false");
}

#[test]
fn test_set_remove_preserves_other() {
    // If s.contains(3) and s.contains(5), removing 5 should preserve 3.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    // Require non-empty set to satisfy remove overflow checks (#2154)
    ctx.push_obligation(ProofObligation::assume("len_pos", "s.len() > 0"));
    ctx.push_obligation(ProofObligation::assume("has_3", "s.contains(3)"));
    ctx.push_obligation(ProofObligation::assume("has_5", "s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "still_has_3",
        "s.remove(5).contains(3)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "s.remove(5) should preserve s.contains(3)");
}

/// Remove on unconstrained set (may be empty) should verify: remove(5) stores
/// false at key 5, so contains(5) is false regardless of initial state.
/// With unsigned BV pointer_width lengths (#1745), the non-negative length
/// check is trivially true, so no overflow counterexample fires.
/// Updated from #2171 regression guard to match unsigned semantics.
#[test]
fn test_set_remove_unconstrained_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    // Do NOT assume s.len() > 0 — leave unconstrained
    ctx.push_obligation(ProofObligation::assert(
        "removed",
        "!s.remove(5).contains(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "remove(5) on any set should make contains(5) false",
    );
}

#[test]
fn test_set_choose_contains_when_nonempty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("nonempty", "s.len() > 0usize"));
    ctx.push_obligation(ProofObligation::assert(
        "choose_member",
        "s.contains(s.choose())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Set::choose should be known contained when len() > 0",
    );
}

#[test]
fn test_set_finite_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assert("finite", "s.finite()"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Set::finite should verify for finite-backend element domains",
    );
}

#[test]
fn test_set_finite_unbounded_element_domain_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<nat>"));
    ctx.push_obligation(ProofObligation::assert("finite", "s.finite()"));

    let result = AYEncoder::verify(&ctx);
    match result {
        crate::encoder::VerifyResult::Error { message } => assert!(
            message.contains("Set::finite() is unsupported for Set<nat>"),
            "Set<nat>.finite() should fail closed with a finite-cardinality diagnostic, got: {message}",
        ),
        other => panic!(
            "Set<nat>.finite() should fail closed as an Error for unbounded domains, got {other:?}"
        ),
    }
}

#[test]
fn test_set_finite_unbounded_element_domain_assumption_encodes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<nat>"));
    ctx.push_obligation(ProofObligation::assume("finite", "s.finite()"));
    ctx.push_obligation(ProofObligation::assert("trivial", "true"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Set<nat>::finite() should be accepted as an assumption without adding cardinality facts",
    );
}

#[test]
fn test_set_finite_unbounded_assumption_does_not_imply_choose_membership() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<nat>"));
    ctx.push_obligation(ProofObligation::assume("finite", "s.finite()"));
    ctx.push_obligation(ProofObligation::assert(
        "choose_member",
        "s.contains(s.choose())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Set<nat>::finite() assumption alone must not imply choose membership",
    );
}

#[test]
fn test_set_choose_contains_with_unbounded_finite_assumption_and_nonempty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<nat>"));
    ctx.push_obligation(ProofObligation::assume("finite", "s.finite()"));
    ctx.push_obligation(ProofObligation::assume("nonempty", "s.len() > 0usize"));
    ctx.push_obligation(ProofObligation::assert(
        "choose_member",
        "s.contains(s.choose())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Set<nat>::finite() precondition plus len() > 0 should admit choose membership",
    );
}

#[test]
fn test_set_choose_contains_with_finite_and_nonempty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("finite", "s.finite()"));
    ctx.push_obligation(ProofObligation::assume("nonempty", "s.len() > 0usize"));
    ctx.push_obligation(ProofObligation::assert(
        "choose_member",
        "s.contains(s.choose())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Set::choose should be known contained when finite and len() > 0",
    );
}

#[test]
fn test_set_choose_contains_with_explicit_member_witness() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("has_5", "s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "choose_member",
        "s.contains(s.choose())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Set::choose should use an explicit member witness for membership",
    );
}

#[test]
fn test_set_choose_without_nonempty_assumption_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assert(
        "choose_member",
        "s.contains(s.choose())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Set::choose must not imply membership without a witness or len() > 0",
    );
}

#[test]
fn test_set_empty_choose_membership_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "empty_choose_member",
        "trust_vc_types::Set::<i32>::empty()
            .contains(trust_vc_types::Set::<i32>::empty().choose())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Set::empty().choose() must not prove membership in the empty set",
    );
}

#[test]
fn test_set_choose_with_member_witness_does_not_require_len_metadata() {
    use crate::ir::{CollectionOp, TrustVcExpr, TrustVcType};
    use ay_dpll::api::{ArraySort, Logic, Sort};

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let mut choose_registry = std::collections::HashMap::new();

    let elem_ty = TrustVcType::Int { width: 32 };
    let set_ty = TrustVcType::Set(Box::new(elem_ty.clone()));
    let set_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(32),
        element_sort: Sort::Bool,
    }));
    let set_term = solver.declare_const("s", set_sort);
    variables.insert("s".to_string(), set_term);
    var_types.insert("s".to_string(), set_ty.clone());

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.choose_registry = Some(&mut choose_registry);

    let choose_expr = TrustVcExpr::CollectionOp {
        op: CollectionOp::Choose,
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".to_string(),
            ty: set_ty,
        }),
        receiver_name: Some("s".to_string()),
        args: vec![],
        ty: elem_ty,
    };
    let chosen = parser
        .encode_trust_vc_expr(&choose_expr)
        .expect("Set::choose should encode without length metadata");

    let five = parser.solver.try_bv_const(5, 32).unwrap();
    let witness_member = parser.solver.try_select(set_term, five).unwrap();
    parser.solver.try_assert_term(witness_member).unwrap();

    let chosen_member = parser.solver.try_select(set_term, chosen).unwrap();
    let not_chosen_member = parser.solver.try_not(chosen_member).unwrap();
    parser.solver.try_assert_term(not_chosen_member).unwrap();

    let result = parser.solver.check_sat();
    assert!(
        result.is_unsat(),
        "explicit Set member witness should constrain choose membership without length metadata; got {result:?}",
    );
}

// ========================================================================
// Set operations — quantifier-based encodings (#1748)
// ========================================================================

/// DISCRIMINATING: Set::union encodes as forall x: result[x] = s1[x] OR s2[x].
/// If s1.contains(1) and s2.contains(2), their union should contain both.
#[test]
fn test_set_union_contains_elements_from_both() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("s1_has_1", "s1.contains(1)"));
    ctx.push_obligation(ProofObligation::assume("s2_has_2", "s2.contains(2)"));
    ctx.push_obligation(ProofObligation::assert(
        "union_has_1",
        "s1.union(s2).contains(1)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "union of {{1}} and {{2}} should contain 1");
}

/// DISCRIMINATING: Set::union should NOT verify false membership.
/// If s1 = {1} and s2 = {2}, union should not contain 3.
#[test]
fn test_set_union_does_not_contain_absent_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("s1_only_1", "s1.contains(1)"));
    ctx.push_obligation(ProofObligation::assume("s1_not_3", "!s1.contains(3)"));
    ctx.push_obligation(ProofObligation::assume("s2_only_2", "s2.contains(2)"));
    ctx.push_obligation(ProofObligation::assume("s2_not_3", "!s2.contains(3)"));
    ctx.push_obligation(ProofObligation::assert(
        "union_has_3",
        "s1.union(s2).contains(3)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "union of {1} and {2} containing 3");
}

/// DISCRIMINATING: Set::intersect should contain only common elements.
/// {1,2} ∩ {2,3} should contain 2 but not 1.
#[test]
fn test_set_intersect_contains_common() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("s1_has_2", "s1.contains(2)"));
    ctx.push_obligation(ProofObligation::assume("s2_has_2", "s2.contains(2)"));
    ctx.push_obligation(ProofObligation::assert(
        "intersect_has_2",
        "s1.intersect(s2).contains(2)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "intersect of {{..2..}} and {{..2..}} should contain 2",
    );
}

/// DISCRIMINATING: Set::intersect should NOT contain non-common elements.
#[test]
fn test_set_intersect_excludes_non_common() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("s1_has_1", "s1.contains(1)"));
    ctx.push_obligation(ProofObligation::assume("s2_not_1", "!s2.contains(1)"));
    ctx.push_obligation(ProofObligation::assert(
        "intersect_has_1",
        "s1.intersect(s2).contains(1)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "intersect containing element present only in s1");
}

/// DISCRIMINATING: Set::difference: s1 \ s2 contains elements in s1 not in s2.
#[test]
fn test_set_difference_contains_exclusive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("s1_has_1", "s1.contains(1)"));
    ctx.push_obligation(ProofObligation::assume("s2_not_1", "!s2.contains(1)"));
    ctx.push_obligation(ProofObligation::assert(
        "diff_has_1",
        "s1.difference(s2).contains(1)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "difference: 1 in s1 but not s2 should be in result",
    );
}

/// DISCRIMINATING: Set::difference excludes common elements.
#[test]
fn test_set_difference_excludes_common() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("s1_has_2", "s1.contains(2)"));
    ctx.push_obligation(ProofObligation::assume("s2_has_2", "s2.contains(2)"));
    ctx.push_obligation(ProofObligation::assert(
        "diff_has_2",
        "s1.difference(s2).contains(2)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "difference containing element common to both sets");
}

/// Set::subset encodes without error using Int-sorted forall (#1757).
#[test]
fn test_set_subset_encodes_without_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assert("check", "s1.subset(s2)"));

    let result = AYEncoder::verify(&ctx);
    // Encoding test — ay-dpll may return Unknown for set subset (#2229 triage)
    expect_encodes_without_error(&result, "Set::subset");
}

/// Set::superset encodes without error using Int-sorted forall (#1757).
#[test]
fn test_set_superset_encodes_without_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assert("check", "s1.superset(s2)"));

    let result = AYEncoder::verify(&ctx);
    // Encoding test — ay-dpll may return Unknown for set superset (#2229 triage)
    expect_encodes_without_error(&result, "Set::superset");
}

/// subset(other) returns Bool (not Error), even for unconstrained sets.
/// The encoding produces a valid quantified formula that the solver can process.
#[test]
fn test_set_subset_unconstrained_not_verified() {
    // Unconstrained s1 and s2: s1.subset(s2) should not verify (no reason
    // to believe arbitrary s1 is a subset of arbitrary s2).
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s1", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("s2", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assert("check", "s1.subset(s2)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Unconstrained s1.subset(s2)");
}

/// MBQI-free subset propagation: with the native `set.subset` flip, an
/// asserted-true `s.subset(t)` plus a ground membership witness `s.contains(5)`
/// forces `t.contains(5)` by the finite-set theory's ground-witness saturation
/// rule — no quantifier instantiation. Under the prior `forall x. ...` encoding
/// this obligation depended on MBQI/e-matching to instantiate the universal at
/// the witness; it now decides natively in QF_SETLIA.
#[test]
fn test_set_subset_membership_propagates_to_superset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("t", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("sub", "s.subset(t)"));
    ctx.push_obligation(ProofObligation::assume("has_5", "s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert("t_has_5", "t.contains(5)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "s ⊆ t and 5 ∈ s should prove 5 ∈ t via native set.subset (no MBQI)",
    );
}

/// Soundness guard for the native subset flip: an asserted-true `s.subset(t)`
/// with a witness `e ∈ s` must NOT prove membership of a *different* witnessed
/// element. `5 ∈ s` and `s ⊆ t` say nothing about whether `7 ∈ t`.
#[test]
fn test_set_subset_does_not_overpropagate_membership() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("t", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("sub", "s.subset(t)"));
    ctx.push_obligation(ProofObligation::assume("has_5", "s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert("t_has_7", "t.contains(7)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "s ⊆ t and 5 ∈ s must not prove 7 ∈ t");
}

/// MBQI-free superset propagation: superset is encoded as the reversed native
/// `set.subset` atom, so `t.superset(s)` plus `s.contains(5)` proves
/// `t.contains(5)` by the same ground-witness rule.
#[test]
fn test_set_superset_membership_propagates() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("t", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("sup", "t.superset(s)"));
    ctx.push_obligation(ProofObligation::assume("has_5", "s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert("t_has_5", "t.contains(5)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "t ⊇ s and 5 ∈ s should prove 5 ∈ t via reversed native set.subset",
    );
}

// ========================================================================
// Map::insert() (Part of #1748)
// ========================================================================

// ========================================================================
// Map::subset_of() — native `map.subset` flip (no MBQI). Mirrors the Set and
// Multiset native-subset adoption. ay's finite-map theory decides reflexivity
// and the ground subset↔key obligations without quantifier instantiation.
// ========================================================================

/// Reflexivity: `m.subset_of(m)` is valid. ay refutes its negation structurally
/// (no MBQI). Preserved across the native flip.
#[test]
fn test_map_subset_reflexive_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.push_obligation(ProofObligation::assert("refl", "m.subset_of(m)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "m.subset_of(m) should verify (reflexivity, no MBQI)",
    );
}

/// MBQI-free submap membership propagation: with the native `map.subset` flip,
/// an asserted-true `m.subset_of(n)` plus a ground domain witness
/// `m.contains_key(5)` forces `n.contains_key(5)` by the finite-map theory's
/// ground subset↔key obligation — no quantifier instantiation. Under the prior
/// (value-quantified, semantically wrong) encoding this obligation produced a
/// spurious counterexample; it now decides natively in QF_MAPLIA. This is the
/// MBQI obligation the flip unlocks.
#[test]
fn test_map_subset_membership_propagates() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.declare_var_typed(
        "n",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("sub", "m.subset_of(n)"));
    ctx.push_obligation(ProofObligation::assume("has_5", "m.contains_key(5)"));
    ctx.push_obligation(ProofObligation::assert("n_has_5", "n.contains_key(5)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "m ⊆ n and 5 ∈ dom(m) should prove 5 ∈ dom(n) via native map.subset (no MBQI)",
    );
}

/// Soundness guard for the native flip: an asserted-true `m.subset_of(n)` with a
/// witness `5 ∈ dom(m)` must NOT prove membership of a *different* witnessed key.
/// `5 ∈ dom(m)` and `m ⊆ n` say nothing about whether `7 ∈ dom(n)`. The native
/// ground-witness rule fires only at the present witness, never over-propagates.
#[test]
fn test_map_subset_does_not_overpropagate_membership() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.declare_var_typed(
        "n",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("sub", "m.subset_of(n)"));
    ctx.push_obligation(ProofObligation::assume("has_5", "m.contains_key(5)"));
    ctx.push_obligation(ProofObligation::assert("n_has_7", "n.contains_key(7)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "m ⊆ n and 5 ∈ dom(m) must not prove 7 ∈ dom(n)");
}

/// Soundness guard: an unconstrained `m.subset_of(n)` over arbitrary maps does
/// not verify (ground witnesses cannot certify a universal over the unbounded
/// key domain). Fails closed — matching the prior encoding.
#[test]
fn test_map_subset_unconstrained_fail_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.declare_var_typed(
        "n",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.push_obligation(ProofObligation::assert("sub", "m.subset_of(n)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Unconstrained m.subset_of(n) must not verify");
}

#[test]
fn test_map_insert() {
    // m.insert(5, true).get(5) == true
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "inserted",
        "m.insert(5, true).get(5) == true",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "m.insert(5, true).get(5) should be true");
}

#[test]
fn test_map_insert_preserves_other_keys() {
    // If m.get(3) == true, then m.insert(5, false).get(3) == true.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "key_3_present",
        "m.contains_key(3)",
    ));
    ctx.push_obligation(ProofObligation::assume("key_3", "m.get(3) == true"));
    ctx.push_obligation(ProofObligation::assert(
        "preserved",
        "m.insert(5, false).get(3) == true",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "m.insert(5, false) should preserve m.get(3)");
}

#[test]
fn test_map_insert_then_bracket_index() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "inserted_bracket",
        "m.insert(5, true)[5] == true",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "m.insert(5, true)[5] should be true");
}

#[test]
fn test_map_index_method_matches_get() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "index_matches_get",
        "m.insert(5, true).index(5) == m.insert(5, true).get(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Map::index(k) should match Map::get(k)");
}

#[test]
fn test_map_get_absent_key_requires_contains_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "absent_get_precondition",
        "m.insert(5, true).get(6) == m.insert(5, true).get(6)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Map::get must require contains_key for absent keys",
    );
}

#[test]
fn test_map_index_method_absent_key_requires_contains_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "absent_index_method_precondition",
        "m.insert(5, true).index(6) == m.insert(5, true).index(6)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Map::index method must require contains_key for absent keys",
    );
}

#[test]
fn test_map_bracket_index_wrong_value_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "inserted_wrong_bracket",
        "m.insert(5, true)[5] == false",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "m.insert(5, true)[5] should not be false");
}

#[test]
fn test_map_bracket_index_absent_key_requires_contains_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "absent_bracket_precondition",
        "m.insert(5, true)[6] == m.insert(5, true)[6]",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Map bracket index must require contains_key for absent keys",
    );
}

#[test]
fn test_map_get_absent_key_assumption_requires_contains_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.declare_var_typed("ok", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume(
        "absent_get_assumption",
        "ok == (m.insert(5, true).get(6) == false)",
    ));
    ctx.push_obligation(ProofObligation::assert("after_bad_assumption", "ok"));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "Map::get(k) requires contains_key(k)",
        "Map::get side conditions inside assumptions must be checked",
    );
}

#[test]
fn test_map_index_method_absent_key_assumption_requires_contains_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.declare_var_typed("ok", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume(
        "absent_index_method_assumption",
        "ok == (m.insert(5, true).index(6) == false)",
    ));
    ctx.push_obligation(ProofObligation::assert("after_bad_assumption", "ok"));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "Map::get(k) requires contains_key(k)",
        "Map::index method side conditions inside assumptions must be checked",
    );
}

#[test]
fn test_map_bracket_absent_key_assumption_requires_contains_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.declare_var_typed("ok", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume(
        "absent_bracket_assumption",
        "ok == (m.insert(5, true)[6] == false)",
    ));
    ctx.push_obligation(ProofObligation::assert("after_bad_assumption", "ok"));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "Map::index(k) requires contains_key(k)",
        "Map bracket side conditions inside assumptions must be checked",
    );
}

#[test]
fn test_map_absent_key_return_value_assumption_requires_contains_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.declare_var_typed("result", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume(
        "return_value",
        "result == m.insert(5, true)[6]",
    ));
    ctx.push_obligation(ProofObligation::assert("tautology", "result == result"));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "Map::index(k) requires contains_key(k)",
        "return_value assumptions must check Map bracket side conditions",
    );
}

#[test]
fn test_map_literal_bracket_index() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "literal_bracket",
        "trust_vc_types::map![10i32 => 100i32, 20i32 => 200i32][20i32] == 200i32",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "map! literal bracket index should read inserted value",
    );
}

// ========================================================================
// Map domain tracking — soundness tests (#1966)
// ========================================================================

/// DISCRIMINATING: insert marks key present in domain.
#[test]
fn test_map_insert_then_contains_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "has_key",
        "m.insert(5, true).contains_key(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insert(5, v).contains_key(5) should verify");
}

/// DISCRIMINATING: contains_value witnesses a value through an inserted key.
#[test]
fn test_map_contains_value_inserted_value() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "has_value",
        "trust_vc_types::Map::<i32, i32>::empty().insert(1, 2).insert(2, 4).contains_value(4)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inserted Map value should satisfy contains_value");
}

/// DISCRIMINATING: contains_value should not invent values outside the domain.
#[test]
fn test_map_contains_value_absent_value_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "has_absent_value",
        "trust_vc_types::Map::<i32, i32>::empty().insert(1, 2).insert(2, 4).contains_value(3)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "absent Map value should not satisfy contains_value",
    );
}

/// DISCRIMINATING: overwriting a key removes the old value when no other key has it.
#[test]
fn test_map_contains_value_overwrite_removes_old_value() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "old_value_absent",
        "!trust_vc_types::Map::<i32, i32>::empty().insert(1, 2).insert(1, 3).contains_value(2)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "overwritten Map value should be absent when no other key maps to it",
    );
}

#[test]
fn test_map_ext_eq_same_inserted_map_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "map_ext_eq_same",
        "ext_eq!(
            trust_vc_types::Map::<i32, bool>::empty().insert(5, true),
            trust_vc_types::Map::<i32, bool>::empty().insert(5, true)
        )",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ext_eq! on identical finite Maps should verify without leaking Map::get preconditions",
    );
}

#[test]
fn test_map_ext_eq_same_domain_different_value_fails() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "map_ext_eq_different_value",
        "ext_eq!(
            trust_vc_types::Map::<i32, bool>::empty().insert(5, true),
            trust_vc_types::Map::<i32, bool>::empty().insert(5, false)
        )",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "ext_eq! on Maps with the same key and different value should fail",
    );
}

#[test]
fn test_map_plain_eq_same_inserted_map_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "map_plain_eq_same",
        "trust_vc_types::Map::<i32, bool>::empty().insert(5, true)
            == trust_vc_types::Map::<i32, bool>::empty().insert(5, true)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "plain Map == should use public extensional equality semantics",
    );
}

#[test]
fn test_map_plain_eq_same_domain_different_value_fails() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "map_plain_eq_different_value",
        "trust_vc_types::Map::<i32, bool>::empty().insert(5, true)
            == trust_vc_types::Map::<i32, bool>::empty().insert(5, false)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "plain Map == should refute different values on the same key",
    );
}

#[test]
fn test_map_strict_eq_same_insert_chain_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "map_strict_eq_same_insert_chain",
        "strict_eq!(
            trust_vc_types::Map::<i32, bool>::empty().insert(5, true),
            trust_vc_types::Map::<i32, bool>::empty().insert(5, true)
        )",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "strict_eq! should prove raw equality for identical Map construction",
    );
}

#[test]
fn test_map_equal_alias_same_insert_chain_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "map_equal_alias_same_insert_chain",
        "equal!(
            trust_vc_types::Map::<i32, bool>::empty().insert(5, true),
            trust_vc_types::Map::<i32, bool>::empty().insert(5, true)
        )",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "equal! should alias strict_eq! for identical Map construction",
    );
}

#[test]
fn test_map_plain_eq_different_domain_fails() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "map_plain_eq_different_domain",
        "trust_vc_types::Map::<i32, bool>::empty().insert(5, true)
            == trust_vc_types::Map::<i32, bool>::empty().insert(6, true)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "plain Map == should refute different key domains");
}

#[test]
fn test_set_mk_map_plain_eq_equivalent_functions_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "mk_map_plain_eq_equivalent_functions",
        "trust_vc_types::Set::<i32>::empty()
            .insert(1)
            .insert(2)
            .insert(3)
            .mk_map(trust_vc_types::SpecFn::new(|x: i32| x + 4))
            == trust_vc_types::Set::<i32>::empty()
                .insert(1)
                .insert(2)
                .insert(3)
                .mk_map(trust_vc_types::SpecFn::new(|y: i32| y + (2 + 2)))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "plain Map == should verify equivalent Set::mk_map outputs",
    );
}

#[test]
fn test_set_mk_map_strict_eq_constant_folded_function_model_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "mk_map_strict_eq_constant_folded_function_model",
        "strict_eq!(
            trust_vc_types::Set::<i32>::empty()
                .insert(1)
                .insert(2)
                .insert(3)
                .mk_map(trust_vc_types::SpecFn::new(|x: i32| x + 4)),
            trust_vc_types::Set::<i32>::empty()
                .insert(1)
                .insert(2)
                .insert(3)
                .mk_map(trust_vc_types::SpecFn::new(|y: i32| y + (2 + 2)))
        )",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "strict_eq! should verify the same finite Set::mk_map function model",
    );
}

#[test]
fn test_set_mk_map_strict_eq_equivalent_functions_fails_without_extensionality() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "mk_map_strict_eq_equivalent_functions",
        "strict_eq!(
            trust_vc_types::Set::<i32>::empty()
                .insert(1)
                .insert(2)
                .insert(3)
                .mk_map(trust_vc_types::SpecFn::new(|x: i32| x + 4)),
            trust_vc_types::Set::<i32>::empty()
                .insert(1)
                .insert(2)
                .insert(3)
                .mk_map(trust_vc_types::SpecFn::new(|y: i32| (2 + 2) + y))
        )",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "strict_eq! should not use Map extensional equality for Set::mk_map outputs",
    );
}

#[test]
fn test_set_plain_eq_same_values_verified() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "set_plain_eq_same_values",
        "trust_vc_types::Set::<i32>::empty().insert(1).insert(2)
            == trust_vc_types::Set::<i32>::empty().insert(2).insert(1)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "plain Set == should use extensional equality semantics",
    );
}

#[test]
fn test_set_plain_eq_different_values_fails() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "set_plain_eq_different_values",
        "trust_vc_types::Set::<i32>::empty().insert(1)
            == trust_vc_types::Set::<i32>::empty().insert(2)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "plain Set == should refute different memberships");
}

#[test]
fn test_map_ext_eq_bypass_does_not_disable_public_get_precondition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "public_get_still_checked_after_ext_eq",
        "ext_eq!(
            trust_vc_types::Map::<i32, bool>::empty().insert(5, true),
            trust_vc_types::Map::<i32, bool>::empty().insert(5, true)
        ) && (m.insert(5, true).get(6) == m.insert(5, true).get(6))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "extensional Map equality must not disable public Map::get side conditions",
    );
}

#[test]
fn test_set_mk_map_finite_insert_chain_get_positive() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "finite_mk_map_get",
        "trust_vc_types::Set::<i32>::empty()
            .insert(1)
            .insert(2)
            .insert(3)
            .mk_map(trust_vc_types::SpecFn::new(|k: i32| 10 * k))
            .get(2)
            == 20",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "finite Set::mk_map get should verify");
}

#[test]
fn test_set_mk_map_finite_insert_chain_contains_absent_key_fails() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "finite_mk_map_absent_key",
        "trust_vc_types::Set::<i32>::empty()
            .insert(1)
            .insert(2)
            .insert(3)
            .mk_map(trust_vc_types::SpecFn::new(|k: i32| 10 * k))
            .contains_key(4)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "finite Set::mk_map should reject absent contains_key",
    );
}

#[test]
fn test_set_mk_map_finite_insert_chain_differing_maps_fail() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "finite_mk_map_different_values",
        "trust_vc_types::Set::<i32>::empty()
            .insert(1)
            .insert(2)
            .insert(3)
            .mk_map(trust_vc_types::SpecFn::new(|k: i32| 10 * k))
            .get(1)
            == trust_vc_types::Set::<i32>::empty()
                .insert(1)
                .insert(3)
                .insert(2)
                .mk_map(trust_vc_types::SpecFn::new(|k: i32| 11 * k))
                .get(1)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "finite Set::mk_map should reject differing generated map values",
    );
}

#[test]
fn test_set_mk_map_anonymous_dom_contains_source_key() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "finite_mk_map_dom_has_key",
        "trust_vc_types::Set::<i32>::empty()
            .insert(1)
            .insert(2)
            .insert(3)
            .mk_map(trust_vc_types::SpecFn::new(|k: i32| 10 * k))
            .dom()
            .contains(2)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "anonymous Set::mk_map(...).dom() should use term-keyed domain metadata",
    );
}

#[test]
fn test_set_mk_map_let_bound_dom_contains_source_key() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "finite_mk_map_let_bound_dom_has_key",
        "{
            let generated = trust_vc_types::Set::<i32>::empty()
                .insert(1)
                .insert(2)
                .insert(3)
                .mk_map(trust_vc_types::SpecFn::new(|k: i32| 10 * k));
            generated.dom().contains(2)
        }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "let-bound Set::mk_map(...).dom() should preserve the source set domain",
    );
}

#[test]
fn test_set_mk_map_anonymous_dom_rejects_absent_source_key() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "finite_mk_map_dom_absent_key",
        "trust_vc_types::Set::<i32>::empty()
            .insert(1)
            .insert(2)
            .insert(3)
            .mk_map(trust_vc_types::SpecFn::new(|k: i32| 10 * k))
            .dom()
            .contains(4)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "anonymous Set::mk_map(...).dom() should preserve the source set domain",
    );
}

/// DISCRIMINATING: remove marks key absent in domain.
#[test]
fn test_map_remove_drops_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assume("len_pos", "m.len() > 0"));
    ctx.push_obligation(ProofObligation::assert(
        "removed",
        "!m.insert(5, true).remove(5).contains_key(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "insert(5).remove(5).contains_key(5) should be false",
    );
}

/// DISCRIMINATING: dom().contains() reflects inserted keys.
#[test]
fn test_map_dom_contains_inserted_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "dom_has",
        "m.insert(5, true).dom().contains(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insert(5).dom().contains(5) should verify");
}

/// DISCRIMINATING: remove preserves other keys in domain.
#[test]
fn test_map_remove_preserves_other_keys() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, bool>"),
    );
    ctx.push_obligation(ProofObligation::assume("len_pos", "m.len() > 0"));
    ctx.push_obligation(ProofObligation::assume("has_3", "m.contains_key(3)"));
    ctx.push_obligation(ProofObligation::assert(
        "still_has_3",
        "m.remove(5).contains_key(3)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "remove(5) should preserve contains_key(3)");
}

// ========================================================================
// Set cardinality — exact conditional axioms (#1800 Slice 3)
// ========================================================================

/// DISCRIMINATING: Insert of a NEW element increases set length by exactly 1.
/// s.contains(5) == false ⇒ s.insert(5).len() == s.len() + 1
#[test]
fn test_set_insert_new_element_increases_len() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("len_known", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("not_has_5", "!s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "len_after",
        "s.insert(5).len() == 4",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insert of absent element should increase len by 1");
}

/// DISCRIMINATING: Insert of an EXISTING element does NOT change set length.
/// s.contains(5) == true ⇒ s.insert(5).len() == s.len()
#[test]
fn test_set_insert_existing_element_preserves_len() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("len_known", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("has_5", "s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "len_after",
        "s.insert(5).len() == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insert of existing element should preserve len");
}

/// NEGATIVE: Claiming insert of existing element increases len should FAIL.
#[test]
fn test_set_insert_existing_element_wrong_len_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("len_known", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("has_5", "s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "len_wrong",
        "s.insert(5).len() == 4",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "insert of existing element claiming len+1");
}

/// DISCRIMINATING: Remove of a PRESENT element decreases set length by exactly 1.
/// s.contains(5) == true ⇒ s.remove(5).len() == s.len() - 1
#[test]
fn test_set_remove_present_element_decreases_len() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("len_known", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("has_5", "s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "len_after",
        "s.remove(5).len() == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "remove of present element should decrease len by 1",
    );
}

/// DISCRIMINATING: Remove of an ABSENT element does NOT change set length.
/// s.contains(5) == false ⇒ s.remove(5).len() == s.len()
#[test]
fn test_set_remove_absent_element_preserves_len() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("len_known", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("not_has_5", "!s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "len_after",
        "s.remove(5).len() == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "remove of absent element should preserve len");
}

/// NEGATIVE: Claiming remove of absent element decreases len should FAIL.
#[test]
fn test_set_remove_absent_element_wrong_len_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("len_known", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assume("not_has_5", "!s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "len_wrong",
        "s.remove(5).len() == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "remove of absent element claiming len-1");
}

/// NEGATIVE: Insert of an absent element must not wrap length from MAX to 0.
#[test]
fn test_set_insert_absent_element_does_not_wrap_len_to_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume(
        "len_max",
        "s.len() == 18446744073709551615u64",
    ));
    ctx.push_obligation(ProofObligation::assume("not_has_5", "!s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "len_wraps",
        "s.insert(5).len() == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "insert of absent element wrapping len from MAX to 0",
    );
}

/// NEGATIVE: Remove of a present element must not wrap length from 0 to MAX.
#[test]
fn test_set_remove_present_element_does_not_wrap_len_to_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.push_obligation(ProofObligation::assume("len_zero", "s.len() == 0"));
    ctx.push_obligation(ProofObligation::assume("has_5", "s.contains(5)"));
    ctx.push_obligation(ProofObligation::assert(
        "len_wraps",
        "s.remove(5).len() == 18446744073709551615u64",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "remove of present element wrapping len from 0 to MAX",
    );
}

// ========================================================================
// Map::dom().len() encoding (#1966)
// ========================================================================

/// Map::dom().len() encodes without error with domain tracking (#1966).
#[test]
fn test_map_dom_len_encodes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.push_obligation(ProofObligation::assert("dom_len", "m.dom().len() == 0"));

    let result = AYEncoder::verify(&ctx);
    // dom() returns the domain array; len() on it requires Set length tracking
    // which is not wired for the dom result. Encoding should not error —
    // it may return Counterexample or Unknown depending on length propagation.
    expect_encodes_without_error(&result, "Map::dom().len() with domain tracking");
}
