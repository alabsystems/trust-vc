// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An impl-declared `ensures` now reaches concrete/UFCS callers even when the
//! TRAIT method declares a `requires` — carried as `requires ⟹ ensures`, never
//! unconditionally.
//!
//! ## Before (over-rejection)
//!
//! `assert_impl_postcondition_axioms` skipped any requires-bearing trait method
//! outright, so an entirely ordinary shape lost its postcondition:
//!
//! ```text
//! #[trait_spec] trait W { #[requires(x < 10)] fn w(&self, x: u64) -> u64; }
//! #[trait_impl] impl W for P { #[ensures(result == 1)] fn w(&self, x: u64) -> u64 { 1 } }
//!
//! #[requires(y < 5)] fn f(p: P, y: u64) { assert!(p.w(y) == 1); }  // -> counterexample
//! ```
//!
//! The caller discharges the precondition (`y < 5` ⊨ `y < 10`) and the impl's
//! `ensures` is conformance-checked, yet nothing about `p.w(y)` was in scope.
//! Measured through the production CLI, cache off, at `63e3bcf3`.
//!
//! ## Why the guard, and not simply dropping the skip
//!
//! The conformance pass ASSUMES the trait `requires` before asserting the impl
//! `ensures` (`build_contract_obligations` pushes each `requires` as
//! `ObligationKind::Assume`). The fact it discharges is therefore
//! `requires ⟹ impl_ensures` — NOT the unconditional postcondition. Publishing
//! the unconditional form is a CARDINAL FALSE VERIFY, measured, not reasoned:
//!
//! ```text
//! #[trait_spec] trait W { #[requires(x < 10)] fn w(&self, x: u64) -> u64; }
//! #[trait_impl] impl W for P { #[ensures(result == x)] fn w(&self, x: u64) -> u64 { x % 10 } }
//!
//! #[requires(y >= 10 && y < 100)] fn g(p: P, y: u64) { assert!(p.w(y) == y); }
//! ```
//!
//! `impl W for P { fn w(&self, x: u64) -> u64 { x % 10 } }` compiled and run
//! under stock `rustc --edition 2021` gives `p.w(15) == 5`, so `p.w(y) == y` is
//! FALSE at `y = 15`. With the guard neutered (the `TrustVcExpr::Implies`
//! replaced by the bare conclusion) that assertion VERIFIES on all three call
//! surfaces — receiver, `W::w(&p, y)` and `<P as W>::w(&p, y)`. `outside_*`
//! below are that bite check, frozen.
//!
//! A `requires` clause that fails to lower against the minimal
//! (self/result/params) env drops the WHOLE axiom. Keeping the conclusion after
//! losing the premise is exactly the unsound direction above.
//!
//! ## Scope, stated so it is not mistaken for a wider claim
//!
//! An impl method with its OWN `requires` never reaches this axiom at all:
//! `capture_conformance_method_body` declines on it, so no body is captured and
//! no `impl_ensures` is registered. `impl_own_requires_stays_fail_closed` pins
//! that this change did not quietly widen it.

use trust_vc_core::{verify_function_from_file, verify_trait_conformance_obligation, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut path = std::env::temp_dir();
    path.push(format!("tvc_reqguard_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&path, src).expect("write fixture");
    let result =
        verify_function_from_file(path.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&path);
    result
}

fn conformance(tmp_id: &str, obligation: &str, src: &str) -> VerifyResult {
    let mut path = std::env::temp_dir();
    path.push(format!("tvc_reqguard_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&path, src).expect("write fixture");
    let result = verify_trait_conformance_obligation(path.to_str().expect("utf8 path"), obligation)
        .unwrap_or_else(|e| VerifyResult::Error {
            message: e.to_string(),
        });
    let _ = std::fs::remove_file(&path);
    result
}

/// Deliberately stricter than `!Verified`: an `Error` would mean the obligation
/// stopped being CHECKED, which hollows the guard out — it would "pass" while
/// testing nothing.
fn assert_not_verified(label: &str, result: VerifyResult) {
    if matches!(result, VerifyResult::Verified) {
        panic!("{label} — it VERIFIED");
    }
}

fn assert_verified(label: &str, result: VerifyResult) {
    if !matches!(result, VerifyResult::Verified) {
        panic!("{label} Got: {result:?}");
    }
}

// ---------------------------------------------------------------------------
// The capability: a requires-bearing trait method no longer loses the impl's
// `ensures` at the call site.
// ---------------------------------------------------------------------------

const TRAIT_REQUIRES_IMPL_ENSURES: &str = r#"
#[trust_vc::trait_spec]
trait W { #[trust_vc::requires(x < 10u64)] fn w(&self, x: u64) -> u64; }
struct P;
#[trust_vc::trait_impl]
impl W for P { #[trust_vc::ensures(result == 1u64)] fn w(&self, x: u64) -> u64 { 1u64 } }
#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn t_pos(p: P, y: u64) { trust_vc::assert!(p.w(y) == 1u64); }
#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn t_neg(p: P, y: u64) { trust_vc::assert!(p.w(y) == 2u64); }
"#;

#[test]
fn requires_bearing_trait_method_still_propagates_the_impl_ensures() {
    assert_verified(
        "a caller that discharges the trait `requires` must gain the impl's `ensures`.",
        verify("pos", "t_pos", TRAIT_REQUIRES_IMPL_ENSURES),
    );
}

#[test]
fn requires_bearing_trait_method_false_claim_not_verified() {
    assert_not_verified(
        "CARDINAL: `p.w(y) == 2` against `ensures(result == 1)` must not verify",
        verify("neg", "t_neg", TRAIT_REQUIRES_IMPL_ENSURES),
    );
}

// ---------------------------------------------------------------------------
// THE GUARD — the pin that separates this fix from a cardinal false verify.
// Neuter the `Implies` and every `outside_*` below flips to Verified.
// ---------------------------------------------------------------------------

/// `w(x) == x % 10`, so the impl's `ensures(result == x)` is TRUE only under
/// the trait's `requires(x < 10)`. Ground truth under stock
/// `rustc --edition 2021`: `p.w(15) == 5`.
const ENSURES_TRUE_ONLY_UNDER_REQUIRES: &str = r#"
#[trust_vc::trait_spec]
trait W { #[trust_vc::requires(x < 10u64)] fn w(&self, x: u64) -> u64; }
struct P;
#[trust_vc::trait_impl]
impl W for P { #[trust_vc::ensures(result == x)] fn w(&self, x: u64) -> u64 { x % 10u64 } }
#[trust_vc::requires(y < 10u64)]
#[trust_vc::ensures(true)]
fn inside_true(p: P, y: u64) { trust_vc::assert!(p.w(y) == y); }
#[trust_vc::requires(y < 10u64)]
#[trust_vc::ensures(true)]
fn inside_false(p: P, y: u64) { trust_vc::assert!(p.w(y) == y + 1u64); }
#[trust_vc::requires(y >= 10u64 && y < 100u64)]
#[trust_vc::ensures(true)]
fn outside_recv(p: P, y: u64) { trust_vc::assert!(p.w(y) == y); }
#[trust_vc::requires(y >= 10u64 && y < 100u64)]
#[trust_vc::ensures(true)]
fn outside_ufcs(p: P, y: u64) { trust_vc::assert!(W::w(&p, y) == y); }
#[trust_vc::requires(y >= 10u64 && y < 100u64)]
#[trust_vc::ensures(true)]
fn outside_qual(p: P, y: u64) { trust_vc::assert!(<P as W>::w(&p, y) == y); }
"#;

#[test]
fn inside_the_precondition_the_impl_ensures_is_usable() {
    assert_verified(
        "`y < 10` discharges the trait `requires`, so `p.w(y) == y` must verify.",
        verify("in_t", "inside_true", ENSURES_TRUE_ONLY_UNDER_REQUIRES),
    );
}

#[test]
fn inside_the_precondition_a_false_claim_is_still_refused() {
    assert_not_verified(
        "CARDINAL: `p.w(y) == y + 1` must not verify",
        verify("in_f", "inside_false", ENSURES_TRUE_ONLY_UNDER_REQUIRES),
    );
}

#[test]
fn outside_the_precondition_receiver_call_gains_nothing() {
    assert_not_verified(
        "CARDINAL: at `y >= 10` the impl was never checked, so `p.w(y) == y` \
         (ground truth 5 at y=15) must not verify",
        verify("out_r", "outside_recv", ENSURES_TRUE_ONLY_UNDER_REQUIRES),
    );
}

#[test]
fn outside_the_precondition_ufcs_call_gains_nothing() {
    assert_not_verified(
        "CARDINAL: `W::w(&p, y) == y` at `y >= 10` must not verify",
        verify("out_u", "outside_ufcs", ENSURES_TRUE_ONLY_UNDER_REQUIRES),
    );
}

#[test]
fn outside_the_precondition_qualified_call_gains_nothing() {
    assert_not_verified(
        "CARDINAL: `<P as W>::w(&p, y) == y` at `y >= 10` must not verify",
        verify("out_q", "outside_qual", ENSURES_TRUE_ONLY_UNDER_REQUIRES),
    );
}

#[test]
fn the_conditional_impl_ensures_is_still_conformance_checked() {
    assert_verified(
        "`x % 10 == x` under `x < 10` — the obligation that JUSTIFIES the axiom \
         must still be discharged.",
        conformance(
            "conf_ok",
            "trait impl conformance W::w for P",
            ENSURES_TRUE_ONLY_UNDER_REQUIRES,
        ),
    );
}

/// The justification is a real check, not a formality: a body that violates its
/// own `ensures` under the `requires` must be refuted by the conformance lane.
const IMPL_LIES_UNDER_ITS_REQUIRES: &str = r#"
#[trust_vc::trait_spec]
trait W { #[trust_vc::requires(x < 10u64)] fn w(&self, x: u64) -> u64; }
struct P;
#[trust_vc::trait_impl]
impl W for P { #[trust_vc::ensures(result == x)] fn w(&self, x: u64) -> u64 { x + 1u64 } }
#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn caller(p: P, y: u64) { trust_vc::assert!(p.w(y) == y); }
"#;

#[test]
fn an_impl_lying_under_its_own_precondition_is_refuted() {
    assert_not_verified(
        "CARDINAL: `x + 1 == x` is false for every `x < 10`; conformance must refuse it",
        conformance(
            "conf_lie",
            "trait impl conformance W::w for P",
            IMPL_LIES_UNDER_ITS_REQUIRES,
        ),
    );
}

// ---------------------------------------------------------------------------
// TWO TYPES, ONE TRAIT — the cross-wire pin. Each impl's contract must answer
// only its own receiver, WITH a `requires` in play.
// ---------------------------------------------------------------------------

const TWO_TYPES_ONE_TRAIT_WITH_REQUIRES: &str = r#"
#[trust_vc::trait_spec]
trait W { #[trust_vc::requires(x < 10u64)] fn w(&self, x: u64) -> u64; }
struct P;
struct Q;
#[trust_vc::trait_impl]
impl W for P { #[trust_vc::ensures(result == 1u64)] fn w(&self, x: u64) -> u64 { 1u64 } }
#[trust_vc::trait_impl]
impl W for Q { #[trust_vc::ensures(result == 2u64)] fn w(&self, x: u64) -> u64 { 2u64 } }
#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn p_true(p: P, y: u64) { trust_vc::assert!(p.w(y) == 1u64); }
#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn p_crosswired(p: P, y: u64) { trust_vc::assert!(p.w(y) == 2u64); }
#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn q_true(q: Q, y: u64) { trust_vc::assert!(q.w(y) == 2u64); }
#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn q_crosswired(q: Q, y: u64) { trust_vc::assert!(q.w(y) == 1u64); }
"#;

#[test]
fn two_types_one_trait_each_receiver_reads_its_own_impl() {
    assert_verified(
        "`p.w(y) == 1` must verify",
        verify("2t_p", "p_true", TWO_TYPES_ONE_TRAIT_WITH_REQUIRES),
    );
    assert_verified(
        "`q.w(y) == 2` must verify",
        verify("2t_q", "q_true", TWO_TYPES_ONE_TRAIT_WITH_REQUIRES),
    );
}

#[test]
fn two_types_one_trait_neither_cross_wired_claim_verifies() {
    assert_not_verified(
        "CARDINAL: `Q`'s ensures must never answer a `P` receiver",
        verify("2t_pc", "p_crosswired", TWO_TYPES_ONE_TRAIT_WITH_REQUIRES),
    );
    assert_not_verified(
        "CARDINAL: `P`'s ensures must never answer a `Q` receiver",
        verify("2t_qc", "q_crosswired", TWO_TYPES_ONE_TRAIT_WITH_REQUIRES),
    );
}

// ---------------------------------------------------------------------------
// NARROWNESS — what this change must NOT have moved.
// ---------------------------------------------------------------------------

/// An impl method carrying its OWN `requires` is declined by
/// `capture_conformance_method_body`, so no body and no `impl_ensures` are ever
/// registered and the caller gains nothing. Unchanged by this fix; pinned so a
/// later widening is a deliberate act.
const IMPL_OWN_REQUIRES: &str = r#"
#[trust_vc::trait_spec]
trait W { fn w(&self, x: u64) -> u64; }
struct P;
#[trust_vc::trait_impl]
impl W for P {
    #[trust_vc::requires(x < 10u64)]
    #[trust_vc::ensures(result == 1u64)]
    fn w(&self, x: u64) -> u64 { 1u64 }
}
#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn caller(p: P, y: u64) { trust_vc::assert!(p.w(y) == 1u64); }
"#;

#[test]
fn impl_own_requires_stays_fail_closed() {
    assert_not_verified(
        "an impl-declared `requires` still declines body capture, so nothing propagates",
        verify("own_req", "caller", IMPL_OWN_REQUIRES),
    );
}

/// The no-`requires` path — the one that already worked — must be untouched in
/// BOTH directions.
const NO_REQUIRES_BASELINE: &str = r#"
#[trust_vc::trait_spec]
trait W { fn w(&self) -> u64; }
struct P;
#[trust_vc::trait_impl]
impl W for P { #[trust_vc::ensures(result == 1u64)] fn w(&self) -> u64 { 1u64 } }
#[trust_vc::ensures(true)]
fn n_pos(p: P) { trust_vc::assert!(p.w() == 1u64); }
#[trust_vc::ensures(true)]
fn n_neg(p: P) { trust_vc::assert!(p.w() == 2u64); }
"#;

#[test]
fn no_requires_baseline_unchanged_both_directions() {
    assert_verified(
        "the pre-existing no-`requires` capability must still verify",
        verify("base_p", "n_pos", NO_REQUIRES_BASELINE),
    );
    assert_not_verified(
        "CARDINAL: the no-`requires` liar must still be refused",
        verify("base_n", "n_neg", NO_REQUIRES_BASELINE),
    );
}

/// A trait that declares BOTH `requires` and its own `ensures` already worked
/// (`assert_trait_postconditions` has carried the implication all along). Pin
/// that the new impl-side axiom did not disturb it.
const TRAIT_SIDE_ENSURES_WITH_REQUIRES: &str = r#"
#[trust_vc::trait_spec]
trait W {
    #[trust_vc::requires(x < 10u64)]
    #[trust_vc::ensures(result == 1u64)]
    fn w(&self, x: u64) -> u64;
}
struct P;
#[trust_vc::trait_impl]
impl W for P { fn w(&self, x: u64) -> u64 { 1u64 } }
#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn s_pos(p: P, y: u64) { trust_vc::assert!(p.w(y) == 1u64); }
#[trust_vc::requires(y < 5u64)]
#[trust_vc::ensures(true)]
fn s_neg(p: P, y: u64) { trust_vc::assert!(p.w(y) == 2u64); }
"#;

#[test]
fn trait_side_ensures_with_requires_unchanged_both_directions() {
    assert_verified(
        "the trait's own `requires ⟹ ensures` axiom must still verify",
        verify("ts_p", "s_pos", TRAIT_SIDE_ENSURES_WITH_REQUIRES),
    );
    assert_not_verified(
        "CARDINAL: the trait-side liar must still be refused",
        verify("ts_n", "s_neg", TRAIT_SIDE_ENSURES_WITH_REQUIRES),
    );
}
