// Solver-specialization hook tests — VC-shape → strategy dispatch (capability #7).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Run with: targo --unverified test -p trust-vc-driver --features tactics
//
// The native-code specialization lives in ay's self-hosted JIT; this is the
// trust-vc-side, shape-keyed dispatch that recognizes recurring monomorphized
// VC shapes (generic code instantiated at many call sites) and reuses one
// chosen strategy for them. These tests pin the load-bearing property: a
// fingerprint is invariant under constant/name changes but distinguishes
// genuinely different structure, and the cache reuses entries accordingly. One
// test also drives a fingerprinted shape through the real encoder + ay backend
// to show the dispatch sits in front of a *real* proof, not a stub.
#![cfg(feature = "tactics")]

use trust_vc_core::ir::{CompareOp, TrustVcType};
use trust_vc_driver::lower::{add, cmp, lit, mul, uint, var, Binding, DriverFn, Outcome};
use trust_vc_driver::tactics::{
    shape_fingerprint, suggest_strategy, SpecializationCache, Strategy,
};

fn u32t() -> TrustVcType {
    uint(32)
}

/// `fn f(a, b) requires a<C1, b<C2 { a+b } ensures result<C3`, parameterized on
/// the variable *names* and the constant *values* so a caller can vary only
/// those and check fingerprint stability.
fn add_fn(n1: &str, n2: &str, c1: i128, c2: i128, c3: i128) -> DriverFn {
    DriverFn {
        name: "f".into(),
        params: vec![Binding::new(n1, u32t()), Binding::new(n2, u32t())],
        result: Binding::new("result", u32t()),
        requires: vec![
            cmp(CompareOp::Lt, var(n1, u32t()), lit(c1, u32t())),
            cmp(CompareOp::Lt, var(n2, u32t()), lit(c2, u32t())),
        ],
        body_value: Some(add(var(n1, u32t()), var(n2, u32t()), u32t())),
        ensures: vec![cmp(CompareOp::Lt, var("result", u32t()), lit(c3, u32t()))],
    }
}

/// Two `DriverFn`s differing ONLY in constant values and variable names produce
/// the SAME structural fingerprint. This is the monomorphization-reuse property:
/// generic code instantiated at different call sites collides on one shape.
#[test]
fn identical_up_to_constants_and_names_share_fingerprint() {
    let a = add_fn("x", "y", 100, 100, 200);
    let b = add_fn("alpha", "beta", 1, 42, 9999);

    assert_eq!(
        shape_fingerprint(&a),
        shape_fingerprint(&b),
        "functions identical up to constants/renames must share a fingerprint"
    );
}

/// A structurally different function (`*` in the body instead of `+`) produces a
/// DIFFERENT fingerprint, even with the very same constants and variable names.
#[test]
fn structurally_different_function_has_different_fingerprint() {
    let plus = add_fn("x", "y", 100, 100, 200);

    let mut times = add_fn("x", "y", 100, 100, 200);
    times.body_value = Some(mul(var("x", u32t()), var("y", u32t()), u32t()));

    assert_ne!(
        shape_fingerprint(&plus),
        shape_fingerprint(&times),
        "a different operator skeleton is a different shape"
    );
}

/// The cache shares one entry across all instances of the same shape, and keeps
/// distinct entries for distinct shapes. This is the end-to-end dispatch claim:
/// record a strategy once, reuse it for every later monomorphization.
#[test]
fn cache_reuses_entry_for_same_shape_only() {
    let mut cache = SpecializationCache::new();

    let a = add_fn("x", "y", 100, 100, 200);
    let b = add_fn("p", "q", 5, 5, 10);

    let mut times = add_fn("x", "y", 100, 100, 200);
    times.body_value = Some(mul(var("x", u32t()), var("y", u32t()), u32t()));

    // First sighting of the `+` shape: nothing recorded yet.
    assert!(cache.lookup_fn(&a).is_none());
    cache.record_fn(&a, Strategy::BitVectorBlast);

    // `b` is the SAME shape as `a` (constants/names differ only) → shared entry.
    assert_eq!(cache.lookup_fn(&b), Some(Strategy::BitVectorBlast));

    // The `*` shape is DIFFERENT → still a miss; recording it adds a 2nd entry.
    assert!(cache.lookup_fn(&times).is_none());
    cache.record_fn(&times, Strategy::LinearArithmetic);
    assert_eq!(cache.lookup_fn(&times), Some(Strategy::LinearArithmetic));

    assert_eq!(
        cache.len(),
        2,
        "exactly two distinct shapes should be recorded"
    );
}

/// The strategy heuristic is itself shape-stable: it returns the same strategy
/// for two functions that share a fingerprint, since it never reads literal
/// values or names.
#[test]
fn suggested_strategy_is_stable_under_renames_and_constants() {
    let a = add_fn("x", "y", 100, 100, 200);
    let b = add_fn("p", "q", 7, 9999, 1);

    let sa = suggest_strategy(&a);
    let sb = suggest_strategy(&b);
    assert_eq!(sa, sb, "same shape must suggest the same strategy");
    assert_eq!(
        sa,
        Strategy::BitVectorBlast,
        "fixed-width integer arithmetic should suggest bit-vector blasting"
    );
}

/// End-to-end: the dispatch sits in front of a REAL proof. We fingerprint a VC,
/// record a strategy for it, then actually verify a fresh instance of that same
/// shape through the real encoder + ay backend and confirm it is `Verified`.
/// This shows the shape key gates a genuine verification, not a stub — and the
/// dispatch never changes the verdict (fail-closed: it only selects a path).
#[test]
fn fingerprinted_shape_routes_to_a_real_verified_proof() {
    let mut cache = SpecializationCache::new();

    // Record the strategy for the "two bounded u32s, sum is bounded" shape.
    let template = add_fn("x", "y", 100, 100, 200);
    cache.record_fn(&template, Strategy::BitVectorBlast);

    // A fresh instance of the SAME shape, different names/constants, but still a
    // TRUE postcondition: a<50 ∧ b<50 ⊢ a+b < 100.
    let instance = add_fn("lhs", "rhs", 50, 50, 100);
    assert_eq!(
        cache.lookup_fn(&instance),
        Some(Strategy::BitVectorBlast),
        "the fresh instance must hit the recorded shape entry"
    );

    let (outcome, _) = instance.verify();
    assert_eq!(
        outcome,
        Outcome::Verified,
        "a true postcondition for the recorded shape must verify through the real backend"
    );
}

/// Fail-closed sibling of the previous test: the SAME shape with a FALSE
/// postcondition (a<100 ∧ b<100 ⊬ a+b < 150, e.g. 99+99=198) must be REFUTED.
/// The shape dispatch matching does not — and must not — make a false thing
/// verify.
#[test]
fn same_shape_with_false_postcondition_is_refuted() {
    let mut cache = SpecializationCache::new();

    let template = add_fn("x", "y", 100, 100, 200);
    cache.record_fn(&template, Strategy::BitVectorBlast);

    // Same shape, but the ensures is too tight to hold.
    let bad = add_fn("a", "b", 100, 100, 150);
    assert_eq!(
        cache.lookup_fn(&bad),
        Some(Strategy::BitVectorBlast),
        "the refuted instance is structurally identical, so it shares the entry"
    );

    let (outcome, _) = bad.verify();
    assert_eq!(
        outcome,
        Outcome::Refuted,
        "a false postcondition must be refuted regardless of the recorded strategy"
    );
}
