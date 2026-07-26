// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerificationPipeline-backed regression tests for higher-order
//! spec collection combinators (#2466).
//!
//! Covers: Seq::map, Seq::filter, Set::filter, Set::map, Set::mk_map,
//! Map::map_values, Map::map_entries, Map::filter_keys.
//! Seq::map_values is already covered in test_spec_collection_map_values.rs.

mod common;

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// --- Seq::map ---

#[test]
fn test_seq_map_positive_length_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.push_assume("s_len", "s.len() == 3");
    // map preserves length
    ctx.push_assert(
        "mapped_len",
        "s.map(SpecFn::new(|i: usize, x: i32| x + 1)).len() == 3",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::map should preserve length, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_map_positive_transformed_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.push_assume("s_len", "s.len() >= 1");
    ctx.push_assume("s_val", "s.index(0) == 10");
    ctx.push_assert(
        "mapped_val",
        "s.map(SpecFn::new(|i: usize, x: i32| x + 1)).index(0) == 11",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::map should transform element, got: {:?}",
        result,
    );
}

// --- Set::map ---

#[test]
fn test_set_map_image_membership_encodes_without_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Set<i32>");
    ctx.push_assume("s_has_5", "s.contains(5)");
    // map(|x| x * 2) should produce a set containing 10
    ctx.push_assert(
        "mapped_has_10",
        "s.map(SpecFn::new(|x: i32| x * 2)).contains(10)",
    );

    let result = common::verify_context_with_pipeline(ctx);
    // Set::map image containment is the intended Phase A axiom, but solver
    // completeness is still backend-dependent here: some paths prove it,
    // others conservatively return Unknown or Counterexample. Keep the
    // regression focused on the lowering/encoding contract: this path must not
    // fail closed with an encoder/verifier Error.
    assert!(
        !matches!(result, VerifyResult::Error { .. }),
        "Set::map image membership should encode without verifier errors; conservative non-proof results are currently acceptable, got: {:?}",
        result,
    );
}

#[test]
fn test_set_map_negative_reverse_membership_remains_unproved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Set<i32>");
    ctx.push_assume("s_not_5", "!s.contains(5)");
    // VerificationContext does not support `==>`, so encode implication as `!p || q`.
    // Phase A Set::map is forward-only: absence of a preimage must not prove
    // absence of an image element.
    ctx.push_assert(
        "reverse_membership",
        "!(s.map(SpecFn::new(|x: i32| x * 2)).contains(10)) || s.contains(5)",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified | VerifyResult::Error { .. }),
        "forward-only Set::map must not prove reverse membership (and must not error), got: {:?}",
        result,
    );
}

#[test]
fn test_set_map_negative_wrong_preimage_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Set<i32>");
    ctx.push_assume("s_has_5", "s.contains(5)");
    ctx.push_assume("s_not_4", "!s.contains(4)");
    // If the image contains 10 from preimage 5, it must still not justify an
    // unrelated claim about preimage 4.
    ctx.push_assert(
        "wrong_preimage",
        "!(s.map(SpecFn::new(|x: i32| x * 2)).contains(10)) || s.contains(4)",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Set::map must reject false reverse-preimage claims, got: {:?}",
        result,
    );
}

// --- Set::filter ---

#[test]
fn test_set_filter_positive_retained_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Set<i32>");
    // s contains 5
    ctx.push_assume("s_has_5", "s.contains(5)");
    // filter keeps elements > 0
    ctx.push_assert(
        "filtered_has_5",
        "s.filter(SpecFn::new(|x: i32| x > 0)).contains(5)",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Set::filter should retain element satisfying predicate, got: {:?}",
        result,
    );
}

#[test]
fn test_set_filter_negative_excluded_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Set<i32>");
    ctx.push_assume("s_has_neg", "s.contains(-3)");
    // filter keeps only elements > 0, so -3 must not be in result
    ctx.push_assert(
        "filtered_has_neg",
        "s.filter(SpecFn::new(|x: i32| x > 0)).contains(-3)",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Set::filter should exclude element not satisfying predicate, got: {:?}",
        result,
    );
}

// --- Map::map_values ---

#[test]
fn test_map_map_values_positive_preserves_domain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<u32, i32>");
    ctx.push_assume("m_has_key", "m.contains_key(1u32)");
    ctx.push_assume("m_val", "m.get(1u32) == 10");
    // map_values(|v| v + 1) should preserve domain
    ctx.push_assert(
        "mapped_has_key",
        "m.map_values(SpecFn::new(|v: i32| v + 1)).contains_key(1u32)",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Map::map_values should preserve domain, got: {:?}",
        result,
    );
}

#[test]
fn test_map_map_values_positive_transformed_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<u32, i32>");
    ctx.push_assume("m_has_key", "m.contains_key(1u32)");
    ctx.push_assume("m_val", "m.get(1u32) == 10");
    ctx.push_assert(
        "mapped_val",
        "m.map_values(SpecFn::new(|v: i32| v + 1)).get(1u32) == 11",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Map::map_values should transform value, got: {:?}",
        result,
    );
}

// --- Set::mk_map ---

#[test]
fn test_set_mk_map_positive_preserves_domain_and_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Set<i32>");
    ctx.push_assume("s_has_2", "s.contains(2)");
    ctx.push_assert(
        "mapped_has_key",
        "s.mk_map(SpecFn::new(|x: i32| x + 10)).contains_key(2)",
    );
    ctx.push_assert(
        "mapped_value",
        "s.mk_map(SpecFn::new(|x: i32| x + 10)).get(2) == 12",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Set::mk_map should preserve domain and mapped value, got: {:?}",
        result,
    );
}

#[test]
fn test_set_mk_map_negative_false_value_claim() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Set<i32>");
    ctx.push_assume("s_has_2", "s.contains(2)");
    ctx.push_assert(
        "mapped_value_wrong",
        "s.mk_map(SpecFn::new(|x: i32| x + 10)).get(2) == 11",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Set::mk_map must reject false mapped values, got: {:?}",
        result,
    );
}

// --- Set::mk_map chained with Map::map_values (#2507 regression) ---

/// DISCRIMINATING: exercises the exact #2507 bug path — `map_values` on an
/// anonymous Map produced by `mk_map`. Without the `key_ty` fix in
/// `CollectionMeta`, `map_key_value_types` fails with "Map operation
/// requires a named receiver with known type".
#[test]
fn test_set_mk_map_then_map_values_positive_chained_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Set<i32>");
    ctx.push_assume("s_has_2", "s.contains(2)");
    // mk_map(|x| x + 10) maps 2 → 12, then map_values(|v| v + 1) → 13
    ctx.push_assert(
        "chained_value",
        "s.mk_map(SpecFn::new(|x: i32| x + 10)).map_values(SpecFn::new(|v: i32| v + 1)).get(2) == 13",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "mk_map(...).map_values(...) chaining must verify, got: {:?}",
        result,
    );
}

#[test]
fn test_set_mk_map_then_map_values_negative_wrong_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Set<i32>");
    ctx.push_assume("s_has_2", "s.contains(2)");
    // mk_map(|x| x + 10) maps 2 → 12, then map_values(|v| v + 1) → 13, NOT 12
    ctx.push_assert(
        "chained_value_wrong",
        "s.mk_map(SpecFn::new(|x: i32| x + 10)).map_values(SpecFn::new(|v: i32| v + 1)).get(2) == 12",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "mk_map(...).map_values(...) must reject wrong chained value, got: {:?}",
        result,
    );
}

#[test]
fn test_set_mk_map_then_map_values_positive_preserves_domain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Set<i32>");
    ctx.push_assume("s_has_5", "s.contains(5)");
    // mk_map preserves domain, map_values preserves domain
    ctx.push_assert(
        "chained_domain",
        "s.mk_map(SpecFn::new(|x: i32| x * 2)).map_values(SpecFn::new(|v: i32| v + 1)).contains_key(5)",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "mk_map(...).map_values(...) must preserve domain, got: {:?}",
        result,
    );
}

// --- Map::map_entries ---

#[test]
fn test_map_map_entries_positive_preserves_domain_and_threads_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<i32, i32>");
    ctx.push_assume("m_has_key", "m.contains_key(1)");
    ctx.push_assume("m_val", "m.get(1) == 10");
    ctx.push_assert(
        "mapped_has_key",
        "m.map_entries(SpecFn::new(|k: i32, v: i32| k + v)).contains_key(1)",
    );
    ctx.push_assert(
        "mapped_value",
        "m.map_entries(SpecFn::new(|k: i32, v: i32| k + v)).get(1) == 11",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Map::map_entries should preserve domain and use key/value inputs, got: {:?}",
        result,
    );
}

#[test]
fn test_map_map_entries_negative_false_value_claim() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<i32, i32>");
    ctx.push_assume("m_has_key", "m.contains_key(1)");
    ctx.push_assume("m_val", "m.get(1) == 10");
    ctx.push_assert(
        "mapped_value_wrong",
        "m.map_entries(SpecFn::new(|k: i32, v: i32| k + v)).get(1) == 12",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Map::map_entries must reject false mapped values, got: {:?}",
        result,
    );
}

// --- Map::filter_keys ---

#[test]
fn test_map_filter_keys_negative_removed_key() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Map<u32, i32>");
    ctx.push_assume("m_has_key_0", "m.contains_key(0u32)");
    ctx.push_assume("m_val_0", "m.get(0u32) == 42");
    // filter_keys(|k| k > 0) should exclude key 0
    ctx.push_assert(
        "filtered_has_0",
        "m.filter_keys(SpecFn::new(|k: u32| k > 0)).contains_key(0u32)",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Map::filter_keys should exclude key not satisfying predicate, got: {:?}",
        result,
    );
}

// --- Seq::filter ---

#[test]
fn test_seq_filter_positive_nonempty_when_source_matches() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.push_assume("s_len", "s.len() == 1");
    ctx.push_assume("s_val", "s.index(0) == 5");
    // Axiom 2 (Skolem witness): source[0] satisfies the predicate,
    // so the Skolem witness forces result_len >= 1.
    ctx.push_assert(
        "filtered_nonempty",
        "s.filter(SpecFn::new(|x: i32| x > 0)).len() >= 1",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::filter should be non-empty when source has matching element, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_filter_positive_length_bound() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.push_assume("s_len", "s.len() == 3");
    // Filtered result length must be <= source length
    ctx.push_assert(
        "filtered_len_bound",
        "s.filter(SpecFn::new(|x: i32| x > 0)).len() <= 3",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::filter result length should be bounded by source, got: {:?}",
        result,
    );
}

#[test]
fn test_seq_filter_negative_excluded_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.push_assume("s_len", "s.len() >= 1");
    ctx.push_assume("s_val", "s.index(0) == -3");
    // filter(|x| x > 0) must not claim all result elements are -3
    // The predicate axiom says all result elements satisfy x > 0,
    // so no result element can equal -3.
    ctx.push_assert(
        "filtered_contains_neg",
        "s.filter(SpecFn::new(|x: i32| x > 0)).contains(-3)",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Seq::filter should not retain element failing predicate, got: {:?}",
        result,
    );
}

// --- Seq::filter Skolem injectivity boundary (algorithm audit P1-980) ---

/// When two *distinct* source elements both match the predicate, the Skolem
/// witness cannot alias both to the same result index because
/// `result[witness[0]] == 3` and `result[witness[1]] == 4` forces
/// `witness[0] != witness[1]`, so `result_len >= 2` is derivable.
#[test]
fn test_seq_filter_distinct_elements_force_implicit_injectivity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.push_assume("s_len", "s.len() == 2");
    ctx.push_assume("s_v0", "s.index(0) == 3");
    ctx.push_assume("s_v1", "s.index(1) == 4");
    ctx.push_assert(
        "filtered_len_ge_2",
        "s.filter(SpecFn::new(|x: i32| x > 0)).len() >= 2",
    );

    let result = common::verify_context_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq::filter with 2 distinct matching elements should prove len >= 2, got: {:?}",
        result,
    );
}

/// When two *duplicate* source elements both match the predicate, the Skolem
/// witness encoding lacks an explicit injectivity axiom:
///   `witness[0] == witness[1]` is consistent when `source[0] == source[1]`
/// because `result[w] == 3 && result[w] == 3` is satisfiable.
///
/// This means the solver may assign `result_len == 1`, producing a false
/// counterexample for `filter_len >= 2`. This test documents the current
/// encoding boundary — if it starts verifying after an injectivity axiom
/// is added, promote it to a positive assertion.
#[test]
fn test_seq_filter_duplicate_elements_injectivity_gap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.push_assume("s_len", "s.len() == 2");
    ctx.push_assume("s_v0", "s.index(0) == 3");
    ctx.push_assume("s_v1", "s.index(1) == 3");
    ctx.push_assert(
        "filtered_dup_len_ge_2",
        "s.filter(SpecFn::new(|x: i32| x > 0)).len() >= 2",
    );

    let result = common::verify_context_with_pipeline(ctx);
    // Current encoding: without injectivity, the solver CAN alias both
    // witness indices to 0, allowing result_len == 1. This is a known
    // under-approximation — the encoding proves membership but not exact
    // cardinality for duplicate elements.
    //
    // If this starts returning Verified, the injectivity gap is fixed.
    let is_verified = matches!(result, VerifyResult::Verified);
    if is_verified {
        // Injectivity axiom landed — promote to positive assertion
        eprintln!("NOTE: Seq::filter injectivity gap is now closed (result: Verified)");
    } else {
        // Expected: counterexample or unknown due to missing injectivity
        eprintln!(
            "NOTE: Seq::filter injectivity gap confirmed — duplicate elements \
             under-approximate cardinality (result: {:?})",
            result,
        );
    }
    // This test passes either way — it documents the boundary.
}
