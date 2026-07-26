// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused TrustVc scout for active upstream recommends.rs harness cases.
//
// Upstream `ensures_forall_recommends_failure` calls a spec function whose body
// is `i + 3 == 20` in a quantified postcondition over 0 <= i < 20, while the
// callee recommends only 0 <= i < 5. The schema-valid executable slice below
// checks concrete in-range witnesses, the false-BODY failures that survive
// independent of recommends, and Rust-valid requires/ensures/assert/assume call
// shapes that TrustVc can extract today. Cases that still return solver Unknown
// are kept out of the expected-case inventory.
//
// ADVISORY RECOMMENDS: Verus treats a callee's `recommends` clause as advisory —
// it is checked only in the callee's OWN recommends pass and NEVER propagated
// into a caller's verdict. TrustVc mirrors this: a substituted callee-recommends
// (even `recommends false`) produces NO caller-side obligation, so the true-body
// `bar_recommends_false` cases below now VERIFY. Their earlier counterexamples
// were solely artifacts of a spurious hard recommends assert. The recommends is
// DROPPED, never assumed: `recommends_false_never_assumed_tripwire` is a
// soundness guard proving a callee `recommends(false)` is never assumed by the
// caller (it must stay a counterexample).
//
// The full upstream file still is not promoted: Verus advisory recommends
// DIAGNOSTIC emission, quantified recommends propagation parity, and the generic
// associated-trait substitution case are not complete.

use trust_vc_types::int;

pub const UPSTREAM_RECOMMENDS_RS_ACTIVE_CASES: &[&str] = &[
    "ensures_forall_recommends_failure",
    "ensures_type_substitutes_issue1566",
];

pub fn upstream_recommends_rs_active_cases() -> &'static [&'static str] {
    UPSTREAM_RECOMMENDS_RS_ACTIVE_CASES
}

pub const RECOMMENDS_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "ensures_forall_recommends_positive_witness",
        "ensures_forall_recommends_failure",
        "verified",
        1,
    ),
    (
        "requires_recommended_source_spec_positive",
        "ensures_forall_recommends_failure",
        "verified",
        1,
    ),
    (
        "assert_recommended_source_spec_positive",
        "ensures_forall_recommends_failure",
        "verified",
        1,
    ),
    (
        "assume_recommended_source_spec_positive",
        "ensures_forall_recommends_failure",
        "verified",
        1,
    ),
    (
        "ensures_forall_recommends_failure",
        "ensures_forall_recommends_failure",
        "counterexample",
        1,
    ),
    (
        "ensures_forall_recommends_quantified_exact_failure",
        "ensures_forall_recommends_failure",
        "counterexample",
        1,
    ),
    (
        "requires_false_recommends_advisory",
        "ensures_type_substitutes_issue1566",
        "verified",
        1,
    ),
    (
        "assert_false_recommends_advisory",
        "ensures_type_substitutes_issue1566",
        "verified",
        1,
    ),
    (
        "assume_false_recommends_advisory",
        "ensures_type_substitutes_issue1566",
        "verified",
        1,
    ),
    (
        "body_call_unscoped_recommends_argument_advisory",
        "ensures_forall_recommends_failure",
        "verified",
        1,
    ),
    (
        "ensures_type_substitutes_false_recommends_advisory",
        "ensures_type_substitutes_issue1566",
        "verified",
        1,
    ),
    (
        "ensures_type_substitutes_exists_recommends_false_advisory",
        "ensures_type_substitutes_issue1566",
        "verified",
        1,
    ),
    (
        "ensures_type_substitutes_issue1566",
        "ensures_type_substitutes_issue1566",
        "counterexample",
        1,
    ),
    (
        "ensures_forall_recommends_quantified_failure",
        "ensures_forall_recommends_failure",
        "verified",
        1,
    ),
    (
        "recommends_false_never_assumed_tripwire",
        "ensures_type_substitutes_issue1566",
        "counterexample",
        1,
    ),
];

pub const RECOMMENDS_RS_ERROR_PATTERNS: &[(&str, &[&str])] = &[];

pub fn recommends_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)]
{
    RECOMMENDS_RS_EXPECTED_CASES
}

pub fn recommends_rs_error_patterns() -> &'static [(&'static str, &'static [&'static str])] {
    RECOMMENDS_RS_ERROR_PATTERNS
}

#[trust_vc::spec]
#[trust_vc::recommends(0 <= i && i < 5)]
fn foo(i: int) -> bool {
    i + 3 == 20
}

#[trust_vc::spec]
#[trust_vc::recommends(0 <= i && i < 5)]
fn recommends_only_foo(i: int) -> bool {
    true
}

#[trust_vc::spec]
#[trust_vc::recommends(i < 5u64)]
fn bounded_true_u64(i: u64) -> bool {
    true
}

#[trust_vc::spec]
#[trust_vc::recommends(false)]
fn bar_recommends_false(_witness: int) -> bool {
    true
}

#[trust_vc::proof]
#[trust_vc::ensures(recommends_only_foo(4))]
fn ensures_forall_recommends_positive_witness() {}

#[trust_vc::proof]
#[trust_vc::requires(recommends_only_foo(4))]
#[trust_vc::ensures(true)]
fn requires_recommended_source_spec_positive() {}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn assert_recommended_source_spec_positive() {
    trust_vc::assert!(recommends_only_foo(4));
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn assume_recommended_source_spec_positive() {
    trust_vc::assume!(recommends_only_foo(4));
    trust_vc::assert!(true);
}

#[trust_vc::proof]
#[trust_vc::ensures(foo(5))]
fn ensures_forall_recommends_failure() {}

// Advisory recommends: an unresolvable body-call recommends argument has no
// obligation to guard, so the call is skipped and the proof verifies (rather
// than failing closed as it did when recommends was a hard obligation).
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn body_call_unscoped_recommends_argument_advisory() {
    bounded_true_u64({
        let scoped: u64 = 17u64;
        scoped
    });
}

#[trust_vc::proof]
#[trust_vc::ensures(forall(|i: int| !(0 <= i && i < 20) || foo(i)))]
fn ensures_forall_recommends_quantified_exact_failure() {}

#[trust_vc::proof]
#[trust_vc::ensures(forall(|i: int| !(0 <= i && i < 20) || recommends_only_foo(i)))]
fn ensures_forall_recommends_quantified_failure() {}

// Advisory recommends: `bar_recommends_false` has `recommends(false)` but a
// true BODY. Because the callee recommends is verdict-neutral (never propagated
// to the caller), these cases verify on the true body. Their former
// counterexamples came SOLELY from the spurious hard recommends assert.
#[trust_vc::proof]
#[trust_vc::ensures(bar_recommends_false(0))]
fn ensures_type_substitutes_false_recommends_advisory() {}

#[trust_vc::proof]
#[trust_vc::ensures(exists(|witness: int| bar_recommends_false(witness)))]
fn ensures_type_substitutes_exists_recommends_false_advisory() {}

#[trust_vc::proof]
#[trust_vc::requires(bar_recommends_false(0))]
#[trust_vc::ensures(true)]
fn requires_false_recommends_advisory() {}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn assert_false_recommends_advisory() {
    trust_vc::assert!(bar_recommends_false(0));
}

#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn assume_false_recommends_advisory() {
    trust_vc::assume!(bar_recommends_false(0));
    trust_vc::assert!(true);
}

// SOUNDNESS TRIPWIRE. Recommends is advisory and must NEVER be assumed by a
// caller. This caller assumes only the callee BODY (`true`) via its `requires`,
// so the `ensures(false)` postcondition is unprovable and this MUST stay a
// counterexample. If a callee `recommends(false)` ever leaked into the caller's
// assumptions (e.g. a naive downgrade to a `Recommends`-kind obligation, which
// is ASSUMED at BodyLevel), this would flip to `verified` — an unsoundness.
#[trust_vc::proof]
#[trust_vc::requires(bar_recommends_false(0))]
#[trust_vc::ensures(false)]
fn recommends_false_never_assumed_tripwire() {}

// Upstream `ensures_type_substitutes_issue1566` still requires trigger,
// existential, uninterpreted spec-function, and callee recommends propagation
// parity. The associated-trait generic substitution surface has focused compile
// and VC extraction coverage in `recommends_trait_surface_blocker`; keeping it
// in this direct-source file currently makes unrelated `foo` checks go
// solver-unknown, so this case remains a local fail-closed contradiction.
#[trust_vc::ensures(forall(|witness: int| false || witness != witness))]
fn ensures_type_substitutes_issue1566() {}
