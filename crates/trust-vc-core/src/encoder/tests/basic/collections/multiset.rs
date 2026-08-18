//! Multiset encoding tests — insert, remove, count, contains, union, intersect.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2421 Slice 2.

use super::*;

// ========================================================================
// Multiset::count()
// ========================================================================

#[test]
fn test_multiset_count_after_insert_is_positive() {
    // ms.insert(5).count(5) > 0 should verify (count was 0, now 1)
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
    expect_verified(&result, "ms.insert(5).count(5) > 0 should verify");
}

#[test]
fn test_multiset_count_after_insert_increments_by_one() {
    // ms.insert(5).count(5) == ms.count(5) + 1
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("bounded", "ms.count(5) < 100"));
    ctx.push_obligation(ProofObligation::assert(
        "increments",
        "ms.insert(5).count(5) == ms.count(5) + 1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insert should increment count by 1");
}

#[test]
fn test_multiset_count_is_nonnegative_nat() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assert("count_nat", "ms.count(5) >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Multiset::count should be Nat/nonnegative Int");
}

#[test]
fn test_multiset_bool_insert_count_increments_by_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<bool>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "bounded",
        "ms.count(true) < 100u64",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "increments",
        "ms.insert(true).count(true) == ms.count(true) + 1u64",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Multiset<bool> insert should increment count");
}

#[test]
fn test_multiset_u64_element_insert_count_increments_by_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<u64>"),
    );
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("bounded", "ms.count(x) < 100u64"));
    ctx.push_obligation(ProofObligation::assert(
        "increments",
        "ms.insert(x).count(x) == ms.count(x) + 1u64",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Multiset<u64> should support u64 element count and insert",
    );
}

#[test]
fn test_multiset_u64_unsuffixed_literal_count_zero_assumption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<u64>"),
    );
    ctx.push_obligation(ProofObligation::assume("empty_5", "ms.count(5) == 0u64"));
    ctx.push_obligation(ProofObligation::assert("count_5", "ms.count(5) == 0u64"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Multiset<u64>::count should coerce an unsuffixed literal element",
    );
}

#[test]
fn test_multiset_u64_unsuffixed_literal_insert_count_is_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<u64>"),
    );
    ctx.push_obligation(ProofObligation::assume("empty_5", "ms.count(5) == 0u64"));
    ctx.push_obligation(ProofObligation::assert(
        "insert_count",
        "ms.insert(5).count(5) == 1u64",
    ));

    let result = AYEncoder::verify(&ctx);
    // `insert(5)` is a `store`, so `count(5)` reads back through the array theory
    // as `old_count + 1 = 0 + 1 = 1` — a ground fact (compositional `count`, #2779).
    expect_verified(
        &result,
        "Multiset<u64>::insert(5).count(5) == 1 holds given count(5) == 0",
    );
}

#[test]
fn test_multiset_u64_unsuffixed_literal_remove_count_decrements() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<u64>"),
    );
    ctx.push_obligation(ProofObligation::assume("count_5", "ms.count(5) == 2u64"));
    ctx.push_obligation(ProofObligation::assert(
        "remove_count",
        "ms.remove(5).count(5) == 1u64",
    ));

    let result = AYEncoder::verify(&ctx);
    // `remove(5)` is a `store` to `ite(count > 0, count - 1, 0) = 1`, read back
    // as a ground fact through the array theory (compositional `count`, #2779).
    expect_verified(
        &result,
        "Multiset<u64>::remove(5).count(5) == 1 holds given count(5) == 2",
    );
}

#[test]
fn test_multiset_usize_unsuffixed_literal_insert_remove_round_trip_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<usize>"),
    );
    ctx.push_obligation(ProofObligation::assume("count_5", "ms.count(5) == 7u64"));
    ctx.push_obligation(ProofObligation::assert(
        "round_trip_count",
        "ms.insert(5).remove(5).count(5) == ms.count(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Multiset<usize> insert/remove/count should consistently coerce unsuffixed literal elements",
    );
}

#[test]
fn test_multiset_type_param_insert_count_increments_by_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ms", crate::ir::TrustVcType::parse_or_opaque("Multiset<T>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::TypeParam("T".to_string()));
    ctx.push_obligation(ProofObligation::assume("empty_x", "ms.count(x) == 0u64"));
    ctx.push_obligation(ProofObligation::assert(
        "increments",
        "ms.insert(x).count(x) == 1u64",
    ));

    let result = AYEncoder::verify(&ctx);
    // Generic element `x`: `insert(x).count(x) == old + 1 == 1` is a ground array
    // store/select fact and verifies (compositional `count`, #2779).
    expect_verified(
        &result,
        "Multiset<T>::insert(x).count(x) == 1 holds given count(x) == 0",
    );
}

#[test]
fn test_multiset_type_param_insert2_unconstrained_ext_eq_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::TypeParam("T".to_string()));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::TypeParam("T".to_string()));
    ctx.push_obligation(ProofObligation::assert(
        "generic_insert2_ext_eq",
        "ext_eq!(
            trust_vc_types::Multiset::<T>::empty().insert(a).insert(b),
            trust_vc_types::Multiset::<T>::empty().insert(b).insert(a)
        )",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "generic double insert should commute extensionally without a distinctness precondition",
    );
}

#[test]
fn test_multiset_type_param_duplicate_insert_permutation_ext_eq_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::TypeParam("T".to_string()));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::TypeParam("T".to_string()));
    ctx.push_obligation(ProofObligation::assert(
        "generic_duplicate_insert_permutation_ext_eq",
        "ext_eq!(
            trust_vc_types::Multiset::<T>::empty().insert(a).insert(a).insert(b),
            trust_vc_types::Multiset::<T>::empty().insert(b).insert(a).insert(a)
        )",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "finite-support multiset equality must retain duplicate multiplicities while commuting inserts",
    );
}

#[test]
fn test_multiset_distinct_singletons_ext_eq_has_model_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("distinct", "a != b"));
    ctx.push_obligation(ProofObligation::assert(
        "distinct_singletons_ext_eq",
        "ext_eq!(
            trust_vc_types::Multiset::<i32>::empty().insert(a),
            trust_vc_types::Multiset::<i32>::empty().insert(b)
        )",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "finite-support multiset equality must expose a model for a missing/distinct key",
    );
}

#[test]
fn test_multiset_type_param_singleton_doubleton_ext_eq_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::TypeParam("T".to_string()));
    ctx.push_obligation(ProofObligation::assert(
        "generic_singleton_doubleton_ext_eq",
        "ext_eq!(
            trust_vc_types::Multiset::<T>::empty().insert(a),
            trust_vc_types::Multiset::<T>::empty().insert(a).insert(a)
        )",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "generic insert extensional equality must distinguish singleton from doubleton",
    );
}

#[test]
fn test_multiset_singleton_doubleton_ext_eq_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert(
        "singleton_doubleton_ext_eq",
        "ext_eq!(
            trust_vc_types::Multiset::<i32>::empty().insert(a),
            trust_vc_types::Multiset::<i32>::empty().insert(a).insert(a)
        )",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "finite-support multiset equality must expose a model for unequal multiplicities",
    );
}

// ========================================================================
// Multiset::insert()
// ========================================================================

#[test]
fn test_multiset_insert_contains() {
    // ms.insert(5).contains(5) should be true
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("bounded", "ms.count(5) < 100"));
    ctx.push_obligation(ProofObligation::assert(
        "inserted",
        "ms.insert(5).contains(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ms.insert(5).contains(5) should verify");
}

#[test]
fn test_multiset_insert_preserves_other_counts() {
    // ms.insert(5).count(3) == ms.count(3)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("bounded", "ms.count(5) < 100"));
    ctx.push_obligation(ProofObligation::assert(
        "preserves",
        "ms.insert(5).count(3) == ms.count(3)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insert(5) should preserve count(3)");
}

// ========================================================================
// Multiset::remove()
// ========================================================================

#[test]
fn test_multiset_remove_decrements_positive_count() {
    // If ms.count(5) > 0, ms.remove(5).count(5) == ms.count(5) - 1
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("has_5", "ms.count(5) > 0"));
    ctx.push_obligation(ProofObligation::assert(
        "decrements",
        "ms.remove(5).count(5) == ms.count(5) - 1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "remove should decrement count when positive");
}

#[test]
fn test_multiset_remove_at_zero_stays_zero() {
    // If ms.count(5) == 0, ms.remove(5).count(5) == 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("zero_5", "ms.count(5) == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "still_zero",
        "ms.remove(5).count(5) == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "remove at count 0 should stay 0");
}

#[test]
fn test_multiset_remove_preserves_other_counts() {
    // ms.remove(5).count(3) == ms.count(3)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("has_5", "ms.count(5) > 0"));
    ctx.push_obligation(ProofObligation::assert(
        "preserves",
        "ms.remove(5).count(3) == ms.count(3)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "remove(5) should preserve count(3)");
}

// ========================================================================
// Multiset::contains() (regression: already works, verify still works)
// ========================================================================

#[test]
fn test_multiset_contains_iff_count_positive() {
    // ms.contains(5) iff ms.count(5) > 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("has_5", "ms.count(5) > 0"));
    ctx.push_obligation(ProofObligation::assert("contains_5", "ms.contains(5)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "count > 0 should imply contains");
}

// ========================================================================
// Multiset::choose()
// ========================================================================

#[test]
fn test_multiset_choose_contains_when_nonempty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("nonempty", "ms.len() != 0"));
    ctx.push_obligation(ProofObligation::assert(
        "choose_member",
        "ms.contains(ms.choose())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Multiset::choose should be known to be contained when len != 0",
    );
}

#[test]
fn test_multiset_choose_count_positive_when_nonempty() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("nonempty", "ms.len() != 0"));
    ctx.push_obligation(ProofObligation::assert(
        "choose_count",
        "ms.count(ms.choose()) > 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Multiset::choose should expose a positive count when len != 0",
    );
}

#[test]
fn test_multiset_forall_count_zero_implies_len_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "all_counts_zero",
        "forall(|k: i32| ms.count(k) == 0u64)",
    ));
    ctx.push_obligation(ProofObligation::assert("len_zero", "ms.len() == 0usize"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall zero counts plus choose witness should imply len == 0",
    );
}

#[test]
fn test_multiset_choose_count_zero_implies_len_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "choose_count_zero",
        "ms.count(ms.choose()) == 0usize",
    ));
    ctx.push_obligation(ProofObligation::assert("len_zero", "ms.len() == 0usize"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "zero count at choose witness should imply len == 0",
    );
}

#[test]
fn test_multiset_choose_without_nonempty_assumption_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "choose_member",
        "ms.contains(ms.choose())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Multiset::choose must not imply membership without len != 0",
    );
}

#[test]
fn test_multiset_empty_choose_membership_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "empty_choose_member",
        "trust_vc_types::Multiset::<i32>::empty().contains(trust_vc_types::Multiset::<i32>::empty().choose())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Multiset::empty().choose() must not prove membership in the empty multiset",
    );
}

#[test]
fn test_multiset_choose_after_remove_requires_result_length_metadata() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("source_nonempty", "ms.len() != 0"));
    ctx.push_obligation(ProofObligation::assert(
        "derived_choose_member",
        "ms.remove(5).contains(ms.remove(5).choose())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "requires exact length metadata",
        "Multiset::choose on a derived receiver must not reuse the source length",
    );
}

#[test]
fn test_multiset_choose_after_insert_uses_result_length_metadata() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("bounded_len", "ms.len() < 100"));
    ctx.push_obligation(ProofObligation::assume(
        "bounded_count",
        "ms.count(5) < 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "insert_choose_member",
        "ms.insert(5).contains(ms.insert(5).choose())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Multiset::insert result should carry exact length metadata for choose()",
    );
}

// ========================================================================
// Multiset::union()
// ========================================================================

#[test]
fn test_multiset_union_adds_counts() {
    // ms1.union(ms2).count(5) == ms1.count(5) + ms2.count(5)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "ms1_bounded",
        "forall(|k: i32| ms1.count(k) < 100u64)",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ms2_bounded",
        "forall(|k: i32| ms2.count(k) < 100u64)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "union_adds",
        "ms1.union(ms2).count(5) == ms1.count(5) + ms2.count(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "union should add counts");
}

#[test]
fn test_multiset_add_alias_adds_counts() {
    // Verus spells multiset pointwise sum as add.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "ms1_bounded",
        "forall(|k: i32| ms1.count(k) < 100u64)",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ms2_bounded",
        "forall(|k: i32| ms2.count(k) < 100u64)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "add_adds",
        "ms1.add(ms2).count(5) == ms1.count(5) + ms2.count(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "add should alias union and add counts");
}

#[test]
fn test_multiset_add_ext_eq_union_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "ms1_bounded",
        "forall(|k: i32| ms1.count(k) < 100u64)",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ms2_bounded",
        "forall(|k: i32| ms2.count(k) < 100u64)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "add_union_ext_eq",
        "ext_eq!(ms1.add(ms2), ms1.union(ms2))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Multiset::add should be extensionally equal to union",
    );
}

#[test]
fn test_multiset_add_sub_cancel_ext_eq_under_bounded_counts() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "a",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "b",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "a_bounded",
        "forall(|k: i32| a.count(k) < 100u64)",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "b_bounded",
        "forall(|k: i32| b.count(k) < 100u64)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "add_sub_cancel_ext_eq",
        "ext_eq!(a.add(b).sub(b), a)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bounded add/sub extensional cancellation should use Nat-valued Multiset counts",
    );
}

#[test]
fn test_multiset_direct_eq_add_sub_cancel_under_bounded_counts() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "a",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "b",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "a_bounded",
        "forall(|k: i32| a.count(k) < 100u64)",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "b_bounded",
        "forall(|k: i32| b.count(k) < 100u64)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "add_sub_cancel_eq",
        "a.add(b).sub(b) == a",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "direct add/sub extensional equality should use Nat-valued Multiset counts",
    );
}

#[test]
fn test_multiset_direct_eq_wrong_add_rhs_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "a",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "b",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "a_bounded",
        "forall(|k: i32| a.count(k) < 100u64)",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "b_bounded",
        "forall(|k: i32| b.count(k) < 100u64)",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wrong_rhs_eq",
        "a.add(b) == a.add(a)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "direct Multiset equality must be extensional, not vacuously true",
    );
}

#[test]
fn test_multiset_sub_add_cancel_ext_eq_under_subset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "a",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "b",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("b_subset_a", "b.subset_of(a)"));
    ctx.push_obligation(ProofObligation::assert(
        "sub_add_cancel_ext_eq",
        "ext_eq!(a.sub(b).add(b), a)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sub/add cancellation should be extensionally equal under subset_of",
    );
}

#[test]
fn test_multiset_add_uses_unbounded_nat_counts() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "ms1_max",
        "ms1.count(5) == 18446744073709551615",
    ));
    ctx.push_obligation(ProofObligation::assume("ms2_one", "ms2.count(5) == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "unbounded_sum",
        "ms1.add(ms2).count(5) == 18446744073709551616",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "multiset add should use unbounded Nat counts, not BV64 wraparound",
    );
}

#[test]
fn test_multiset_add_rejects_non_multiset_rhs_before_subset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<u64>"),
    );
    ctx.declare_var_typed(
        "map",
        crate::ir::TrustVcType::parse_or_opaque("Map<u64, u64>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "wrong_add_rhs",
        "ms.add(map).is_subset(ms.add(map))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "Multiset::add should reject non-Multiset operands before subset sees the result",
    );
}

// ========================================================================
// Multiset::intersect()
// ========================================================================

#[test]
fn test_multiset_intersect_takes_minimum() {
    // If ms1.count(5) == 2 and ms2.count(5) == 3, ms1.intersect(ms2).count(5) == 2
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("ms1_count", "ms1.count(5) == 2"));
    ctx.push_obligation(ProofObligation::assume("ms2_count", "ms2.count(5) == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "min_count",
        "ms1.intersect(ms2).count(5) == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "intersect should take minimum count");
}

#[test]
fn test_multiset_intersect_symmetric_minimum() {
    // ms1.intersect(ms2).count(5) == ms2.intersect(ms1).count(5)
    // (both should be min, so they must be equal)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("ms1_c", "ms1.count(5) == 1"));
    ctx.push_obligation(ProofObligation::assume("ms2_c", "ms2.count(5) == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "symmetric",
        "ms1.intersect(ms2).count(5) == ms2.intersect(ms1).count(5)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "intersect should be symmetric");
}

#[test]
fn test_multiset_union_uses_unbounded_nat_counts() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "ms1_max",
        "ms1.count(5) == 18446744073709551615",
    ));
    ctx.push_obligation(ProofObligation::assume("ms2_one", "ms2.count(5) == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "unbounded_sum",
        "ms1.union(ms2).count(5) == 18446744073709551616",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "multiset union should use unbounded Nat counts, not BV64 wraparound",
    );
}

// ========================================================================
// Multiset::difference() / Multiset::sub()  (#2604)
// ========================================================================

#[test]
fn test_multiset_difference_saturating_subtraction() {
    // ms1.count(5) == 3, ms2.count(5) == 1 → ms1.difference(ms2).count(5) == 2
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("ms1_count", "ms1.count(5) == 3"));
    ctx.push_obligation(ProofObligation::assume("ms2_count", "ms2.count(5) == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "diff_count",
        "ms1.difference(ms2).count(5) == 2",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "difference should be saturating subtraction: 3 - 1 == 2",
    );
}

#[test]
fn test_multiset_difference_saturates_at_zero() {
    // ms1.count(5) == 1, ms2.count(5) == 3 → ms1.difference(ms2).count(5) == 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("ms1_count", "ms1.count(5) == 1"));
    ctx.push_obligation(ProofObligation::assume("ms2_count", "ms2.count(5) == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "saturates",
        "ms1.difference(ms2).count(5) == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "difference cannot produce negative counts — saturates at 0",
    );
}

#[test]
fn test_multiset_sub_alias_matches_difference() {
    // ms1.sub(ms2).count(5) should equal ms1.difference(ms2).count(5)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("ms1_count", "ms1.count(5) == 4"));
    ctx.push_obligation(ProofObligation::assume("ms2_count", "ms2.count(5) == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "sub_is_diff",
        "ms1.sub(ms2).count(5) == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sub() should alias difference() with same semantics",
    );
}

#[test]
fn test_multiset_difference_preserves_other_counts() {
    // ms1.difference(ms2).count(3) == ms1.count(3) when only count(5) differs
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("ms2_empty_3", "ms2.count(3) == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "preserves",
        "ms1.difference(ms2).count(3) == ms1.count(3)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "difference with 0 rhs count should preserve lhs count",
    );
}

#[test]
fn test_multiset_sub_add_restores_count_under_subset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "a",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "b",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("b_subset_a", "b.subset_of(a)"));
    ctx.push_obligation(ProofObligation::assert(
        "replacement_count",
        "a.sub(b).add(b).count(k) == a.count(k)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sub/add replacement should restore each count under subset_of",
    );
}

#[test]
fn test_multiset_sub_add_restore_without_subset_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "a",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "b",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert(
        "replacement_count",
        "a.sub(b).add(b).count(k) == a.count(k)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "sub/add replacement must require subset_of to restore counts",
    );
}

#[test]
fn test_multiset_add_sub_reverse_restores_count_under_subset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "a",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "b",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("b_subset_a", "b.subset_of(a)"));
    ctx.push_obligation(ProofObligation::assert(
        "replacement_count",
        "b.add(a.sub(b)).count(k) == a.count(k)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reverse add/sub replacement should restore each count under subset_of",
    );
}

#[test]
fn test_multiset_add_sub_reverse_restore_without_subset_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "a",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "b",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert(
        "replacement_count",
        "b.add(a.sub(b)).count(k) == a.count(k)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "reverse add/sub replacement must require subset_of to restore counts",
    );
}

// ========================================================================
// Multiset::subset_of() / subset() / is_subset()
// ========================================================================

#[test]
fn test_multiset_subset_of_is_reflexive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assert("subset", "ms.subset_of(ms)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Multiset::subset_of should be reflexive");
}

#[test]
fn test_multiset_subset_aliases_are_reflexive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assert("subset", "ms.subset(ms)"));
    ctx.push_obligation(ProofObligation::assert("is_subset", "ms.is_subset(ms)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "subset() and is_subset() should alias reflexive Multiset::subset_of",
    );
}

#[test]
fn test_multiset_subset_of_rejects_larger_lhs_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("ms1_count", "ms1.count(5) == 2"));
    ctx.push_obligation(ProofObligation::assume("ms2_count", "ms2.count(5) == 1"));
    ctx.push_obligation(ProofObligation::assert("bad_subset", "ms1.subset_of(ms2)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "count_lhs(5) > count_rhs(5) should refute Multiset::subset_of",
    );
}

#[test]
fn test_multiset_subset_of_unconstrained_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assert("subset", "ms1.subset_of(ms2)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "unconstrained multisets should not prove subset_of",
    );
}

#[test]
fn test_multiset_large_union_count_uses_nat_arithmetic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "ms1_count_max",
        "ms1.count(5) == 18446744073709551615",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ms2_count_one",
        "ms2.count(5) == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "union_large_count",
        "ms1.union(ms2).count(5) == 18446744073709551616",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "large Multiset union should keep Nat count arithmetic",
    );
}

#[test]
fn test_multiset_large_union_difference_count_uses_nat_arithmetic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms3",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume(
        "ms1_count_max",
        "ms1.count(5) == 18446744073709551615",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ms2_count_one",
        "ms2.count(5) == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ms3_count_one",
        "ms3.count(5) == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wrapped_union_count",
        "ms1.union(ms2).difference(ms3).count(5) == 18446744073709551615",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "large Multiset union wrappers should keep Nat count arithmetic",
    );
}

#[test]
fn test_multiset_subset_of_rejects_non_multiset_rhs() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<u64>"),
    );
    ctx.declare_var_typed("seq", crate::ir::TrustVcType::parse_or_opaque("Seq<u64>"));
    ctx.push_obligation(ProofObligation::assert("wrong_rhs", "ms.subset_of(seq)"));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "Multiset::subset_of should reject a non-Multiset RHS instead of treating any array as counts",
    );
}

#[test]
fn test_multiset_union_rejects_non_multiset_rhs_before_subset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<u64>"),
    );
    ctx.declare_var_typed(
        "map",
        crate::ir::TrustVcType::parse_or_opaque("Map<u64, u64>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "wrong_union_rhs",
        "ms.union(map).is_subset(ms.union(map))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "Multiset::union should reject non-Multiset operands before subset sees the result",
    );
}

// ========================================================================
// Multiset::singleton()  (#2604)
// ========================================================================

#[test]
fn test_multiset_singleton_count_target_is_one() {
    // Multiset::singleton(5).count(5) == 1
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "singleton_count",
        "trust_vc_types::Multiset::<i32>::singleton(5).count(5) == 1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "singleton(5).count(5) should be 1");
}

#[test]
fn test_multiset_singleton_count_other_is_zero() {
    // Multiset::singleton(5).count(3) == 0
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "singleton_other",
        "trust_vc_types::Multiset::<i32>::singleton(5).count(3) == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "singleton(5).count(3) should be 0");
}

#[test]
fn test_multiset_singleton_wrong_target_count_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert(
        "singleton_wrong_count",
        "trust_vc_types::Multiset::<i32>::singleton(a).count(a) == 0usize",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "singleton(a).count(a) == 0 should be rejected");
}

// ========================================================================
// Native multiset-theory decision (count carrier flip).
//
// Subset goals are emitted as a native `(multiset.subset self other)` atom over
// the `Multiset(T) = Array(T -> Int)` count carrier. When the obligation is
// quantifier-free, ay routes it to QF_MSLIA and decides reflexivity and
// ground-witness refutation with NO MBQI. These tests pin the win and its
// fail-closed soundness guard.
// ========================================================================

/// MBQI-free win: a reflexive subset goal carries no other quantifier, so ay's
/// multiset theory refutes its negation structurally (reflexivity), with no
/// universal `forall k. count(m,k) <= count(m,k)` instantiation. Previously this
/// relied on the quantified count-equivalence axiom being E-matched (MBQI).
#[test]
fn test_multiset_subset_reflexive_decides_natively_without_mbqi() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    // No quantified assumption: the only obligation is the subset goal itself,
    // so the formula stays quantifier-free and routes to QF_MSLIA.
    ctx.push_obligation(ProofObligation::assert("refl", "ms.subset_of(ms)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reflexive Multiset::subset_of should decide via the native multiset.subset atom (no MBQI)",
    );
}

/// Ground-witness refutation, also MBQI-free: a single present element witnesses
/// `count(ms1, 5) = 2 > 1 = count(ms2, 5)`, so the native theory refutes the
/// `ms1.subset_of(ms2)` goal over that one ground witness — no quantified axiom.
#[test]
fn test_multiset_subset_ground_witness_refutes_natively() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assume("c1", "ms1.count(5) == 2"));
    ctx.push_obligation(ProofObligation::assume("c2", "ms2.count(5) == 1"));
    ctx.push_obligation(ProofObligation::assert("bad", "ms1.subset_of(ms2)"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "count(ms1,5) > count(ms2,5) at a ground witness should refute subset natively",
    );
}

/// Soundness guard: the native `multiset.subset` procedure never asserts a
/// positive subset from ground saturation over the unbounded element domain, so
/// a fully unconstrained subset goal must NOT verify. This is the sound-or-revert
/// boundary — proving an unconstrained universal from ground witnesses would be
/// the classic unsoundness this flip is forbidden from introducing.
#[test]
fn test_multiset_subset_unconstrained_native_atom_is_sound_fail_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "ms1",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.declare_var_typed(
        "ms2",
        crate::ir::TrustVcType::parse_or_opaque("Multiset<i32>"),
    );
    ctx.push_obligation(ProofObligation::assert(
        "unconstrained",
        "ms1.subset_of(ms2)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "native multiset.subset must not over-decide an unconstrained subset goal",
    );
}
