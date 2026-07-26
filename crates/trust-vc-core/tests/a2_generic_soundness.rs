// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for Phase A2-generic: a GENERIC inherent
//! method called on a CONCRETE receiver instantiation is monomorphized
//! (`A -> u64`) and its conformance-checked contract applied at the call site.
//!
//! The cardinal invariant: never launder an unchecked/unsound contract through
//! monomorphization, and never let a caller read a mismatched impl's body axiom.
//! Every TRUE post-monomorphization fact must VERIFY; every FALSE fact must NOT
//! verify. Also pins the fail-closed guards:
//!   * a method with its OWN generic param stays unresolved (separate axis),
//!   * a method whose contract is false Counterexamples at its own verification
//!     (so it is never trusted), and calling it cannot prove the false ensures.
//!   * binding ORDER is respected (`second` returns B = bool, not A = u64).
//!   * two same-leaf impls of one method fail CLOSED (the registry collision
//!     guard drops both — no concrete UF symbol is defined by two impl bodies),
//!   * while two DISTINCT-leaf structs sharing a method name STILL each
//!     monomorphize independently (the guard fires only on a true leaf clash).
//!
//! See `apply_inherent_impl_methods` / `admit_generic_inherent_impl` /
//! `collect_concrete_receiver_carriers` / `InherentMethodDef::from_impl_method`
//! and the `InherentImplRegistry` collision guard in `vc_extraction.rs`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/a2_generic_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&repro_path(), func)
        .unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

fn assert_verified(func: &str) {
    let v = verdict(func);
    assert!(
        matches!(v, VerifyResult::Verified),
        "`{func}` should verify (monomorphized contract holds); got {v:?}"
    );
}

fn assert_not_verified(func: &str) {
    let v = verdict(func);
    assert!(
        !matches!(v, VerifyResult::Verified),
        "A2-GENERIC FALSE-VERIFY: `{func}` must not verify; got {v:?}"
    );
}

#[test]
fn single_param_true_fact_verifies() {
    assert_verified("take_pos");
}

#[test]
fn multi_param_first_true_fact_verifies() {
    assert_verified("first_pos");
}

#[test]
fn multi_param_second_true_fact_verifies() {
    assert_verified("second_pos");
}

#[test]
fn single_param_false_fact_not_verified() {
    assert_not_verified("take_neg");
}

#[test]
fn multi_param_first_false_fact_not_verified() {
    assert_not_verified("first_neg");
}

#[test]
fn multi_param_second_false_fact_not_verified() {
    // Binding-order guard: if B were bound to u64 (not bool) this could misfire.
    assert_not_verified("second_neg");
}

#[test]
fn broken_contract_counterexamples_at_own_verification() {
    assert_not_verified("take_bad");
}

#[test]
fn broken_contract_not_laundered_through_call_site() {
    assert_not_verified("bad_caller_neg");
}

#[test]
fn own_generic_method_stays_fail_closed() {
    assert_not_verified("own_generic_method_stays_closed");
}

// -- Collision-guard soundness (permanent) ----------------------------------

/// PERMANENT NEGATIVE (moved from the quarantine sentinel when the lane landed):
/// two same-leaf `Wrapper<A>` impls in different modules both declare `pick`
/// (bodies `self.first` vs `self.second`). The registry collision guard drops
/// BOTH — no concrete `Wrapper_u64__pick` symbol is defined by either body — so
/// a caller of `collision_b::Wrapper::<u64>` asserting `w.pick() == first` (FALSE
/// for impl B, whose `pick` returns `self.second == first + 1`) must FAIL CLOSED.
/// A Verified here is the cardinal cross-contamination false-verify.
#[test]
fn same_leaf_method_names_cannot_cross_contaminate() {
    assert_not_verified("same_leaf_method_names_cannot_cross_contaminate");
}

/// POSITIVE CONTROL: the guard fails closed ONLY on a true (base-leaf, method)
/// clash — two DISTINCT-leaf structs (`PickX`, `PickY`) that merely share the
/// method NAME `pick` must STILL each monomorphize and verify.
#[test]
fn distinct_leaf_shared_method_name_still_monomorphizes() {
    assert_verified("distinct_leaf_pick_still_monomorphizes");
}

/// PERMANENT NEGATIVE — the receiver-RESOLVABLE collision that actually
/// exercises the guard end-to-end (`collision_b::Wrapper` above is masked by the
/// struct-literal lowering rejecting a module-qualified receiver). A `shadow`
/// impl declared first would win a naive first-wins registration and launder its
/// `self.b` body onto the top-level `LeafClash` receiver's `LeafClash_u64__grab`
/// symbol, false-verifying `w.grab() == a + 1` (which is FALSE for the top-level
/// type, whose `grab` returns `self.a`). The collision guard drops BOTH `grab`
/// registrations, so this MUST fail closed. Toggling the guard off flips this to
/// Verified — the standing proof that the guard is load-bearing, not incidental.
#[test]
fn resolvable_same_leaf_receiver_cannot_read_shadow_impl_body() {
    assert_not_verified("resolvable_same_leaf_cannot_cross_contaminate");
}

/// NESTED generics: `NOuter::<NInner<u64>>` monomorphizes `get` to return
/// `A = NInner<u64>`, and a field read on the result resolves. A true nested
/// fact verifies; a false one must NOT (a genuine counterexample, kept clear of
/// the `n + 1` overflow-check incompleteness by the `n < 100` bound). Guards the
/// nested-instantiation capability against silent regression.
#[test]
fn nested_generic_instantiation_true_fact_verifies() {
    assert_verified("nested_generic_true_fact");
}

#[test]
fn nested_generic_instantiation_false_fact_not_verified() {
    assert_not_verified("nested_generic_false_fact");
}
