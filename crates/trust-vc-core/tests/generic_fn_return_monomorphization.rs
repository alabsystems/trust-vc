// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Adversarial soundness probes for generic fn-call return-type monomorphization
//! (#2778).
//!
//! The lowering monomorphizes a generic fn's `TypeParam` return into the concrete
//! carrier inferred from the argument types + turbofish, and the encoder bridges
//! the type-erased `Poly` call result back through `Unbox_T` — so a following
//! field projection (`projected.a`) resolves instead of failing closed with
//! `field 'a' on type 'A'`. A guard in `verify_assertion_typed` degrades an
//! under-constrained (no-concrete-witness) SAT model over a generic DATATYPE
//! bridge to Unknown, so an un-instantiated body axiom never surfaces as a
//! spurious counterexample.
//!
//! These probes pin the two soundness invariants in BOTH directions:
//!   * NO false-Verified: every genuinely-FALSE goal is rejected (Counterexample
//!     or Unknown), never Verified.
//!   * NO spurious counterexample on a TRUE goal: every genuinely-TRUE goal is
//!     Verified or honest Unknown, never a Counterexample.
//!
//! Whether a true generic-spec goal lands at Verified or Unknown is
//! context-dependent (it depends on whether ay's ground instantiation fires the
//! Poly body axiom in the surrounding query); both are sound, so the true-goal
//! probes assert "not a counterexample" rather than a single verdict. The
//! reliable, contract-backed gains (exec `#[ensures]` identity, scalar lower
//! bound) are asserted as exact verdicts.

use trust_vc_core::{extract_verification_conditions_with_file_context, VerifyResult};

const SRC: &str = r#"
struct Pair<A, B> { a: A, b: B }
struct Holder { u: u64 }

#[trust_vc::spec]
fn generic_id<A>(value: A) -> A { value }

#[trust_vc::ensures(result == value)]
fn generic_exec_id<A>(value: A) -> A { value }

#[trust_vc::opaque]
#[trust_vc::spec]
fn opaque_id<A>(value: A) -> A { value }

// ---- TRUE goals: never a counterexample ----

#[trust_vc::ensures(true)]
fn exec_true() {
    let value = Pair::<u64, u8> { a: 9u64, b: 2u8 };
    let projected = generic_exec_id::<Pair<u64, u8>>(value);
    trust_vc::assert!(projected.a == 9u64);
    trust_vc::assert!(projected.b == 2u8);
}

#[trust_vc::ensures(true)]
fn spec_true() {
    let value = Pair::<u64, u8> { a: 9u64, b: 2u8 };
    let projected = generic_id::<Pair<u64, u8>>(value);
    trust_vc::assert!(projected.a == 9u64);
    trust_vc::assert!(projected.b == 2u8);
}

#[trust_vc::ensures(true)]
fn scalar_ge0(y: Holder) {
    trust_vc::assert!(generic_id::<u64>(y.u) >= 0u64);
}

#[trust_vc::ensures(true)]
fn scalar_true_symbolic(y: Holder) {
    trust_vc::assert!(generic_id::<u64>(y.u) == y.u);
}

// ---- FALSE goals: never Verified ----

#[trust_vc::ensures(true)]
fn exec_false() {
    let value = Pair::<u64, u8> { a: 9u64, b: 2u8 };
    let projected = generic_exec_id::<Pair<u64, u8>>(value);
    trust_vc::assert!(projected.a == 10u64);
}

#[trust_vc::ensures(true)]
fn spec_false() {
    let value = Pair::<u64, u8> { a: 9u64, b: 2u8 };
    let projected = generic_id::<Pair<u64, u8>>(value);
    trust_vc::assert!(projected.a == 10u64);
}

#[trust_vc::ensures(true)]
fn spec_false_a8() {
    let value = Pair::<u64, u8> { a: 9u64, b: 2u8 };
    let projected = generic_id::<Pair<u64, u8>>(value);
    trust_vc::assert!(projected.a == 8u64);
}

#[trust_vc::ensures(true)]
fn spec_false_b9() {
    let value = Pair::<u64, u8> { a: 9u64, b: 2u8 };
    let projected = generic_id::<Pair<u64, u8>>(value);
    trust_vc::assert!(projected.b == 9u8);
}

// Box/Unbox congruence must NOT collapse two distinct erased values: 9 != 5.
#[trust_vc::ensures(true)]
fn spec_false_two_calls() {
    let p = generic_id::<Pair<u64, u8>>(Pair::<u64, u8> { a: 9u64, b: 2u8 });
    let q = generic_id::<Pair<u64, u8>>(Pair::<u64, u8> { a: 5u64, b: 2u8 });
    trust_vc::assert!(p.a == q.a);
}

// ---- scalar Counterexample stays a Counterexample (concrete witness) ----

#[trust_vc::ensures(true)]
fn scalar_ge1(y: Holder) {
    trust_vc::assert!(generic_id::<u64>(y.u) >= 1u64);
}

#[trust_vc::ensures(true)]
fn scalar_false_eq(y: Holder) {
    trust_vc::assert!(generic_id::<u64>(y.u) == 7u64);
}

// ---- opaque body, unrevealed: fail closed (never Verified) ----

#[trust_vc::ensures(true)]
fn opaque_unrevealed() {
    let value = Pair::<u64, u8> { a: 9u64, b: 2u8 };
    let projected = opaque_id::<Pair<u64, u8>>(value);
    trust_vc::assert!(projected.a == 9u64);
}
"#;

fn verify(case: &str) -> VerifyResult {
    let file = syn::parse_file(SRC).expect("probe source should parse");
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(f) if f.sig.ident == case => Some(f),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist"));
    extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} should extract (no hard lowering error): {err}"))
        .verify()
}

/// EXEC generic-return field projection verifies (the sound gain): the
/// `#[ensures(result == value)]` clause is a ground fact connecting the
/// monomorphized projection to the argument.
#[test]
fn exec_generic_return_field_projection_verifies() {
    assert!(
        matches!(verify("exec_true"), VerifyResult::Verified),
        "exec generic-return field projection should verify, got {:?}",
        verify("exec_true")
    );
}

/// Scalar generic returns are unchanged: a trivially-true lower bound verifies;
/// identity over a symbolic value verifies.
#[test]
fn scalar_generic_return_true_goals_verify() {
    assert!(
        matches!(verify("scalar_ge0"), VerifyResult::Verified),
        "id(y.u) >= 0 should verify, got {:?}",
        verify("scalar_ge0")
    );
    assert!(
        matches!(verify("scalar_true_symbolic"), VerifyResult::Verified),
        "id(y.u) == y.u should verify (sound identity over a symbolic value), got {:?}",
        verify("scalar_true_symbolic")
    );
}

/// No spurious counterexample on a TRUE goal: transparent-spec generic-return
/// field projections on a true goal are Verified or honest Unknown, never a
/// Counterexample. (Verdict is context-dependent; both are sound.)
#[test]
fn true_generic_spec_goals_are_never_counterexamples() {
    for case in ["spec_true", "scalar_true_symbolic"] {
        let result = verify(case);
        assert!(
            !matches!(result, VerifyResult::Counterexample { .. }),
            "{case} is a TRUE goal and must never be a (spurious) counterexample, got {result:?}"
        );
        assert!(
            !matches!(result, VerifyResult::Error { .. }),
            "{case} should no longer hard-error on the field-projection gap, got {result:?}"
        );
    }
}

/// No false-Verified: every genuinely-FALSE generic-return goal is rejected
/// (Counterexample or Unknown), never Verified — including the two-distinct-value
/// case that probes whether the Box/Unbox congruence unsoundly collapses values.
#[test]
fn false_generic_return_goals_are_never_verified() {
    for case in [
        "exec_false",
        "spec_false",
        "spec_false_a8",
        "spec_false_b9",
        "spec_false_two_calls",
        "scalar_ge1",
        "scalar_false_eq",
    ] {
        let result = verify(case);
        assert!(
            matches!(
                result,
                VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
            ),
            "{case} is a FALSE goal and must fail closed (never Verified), got {result:?}"
        );
    }
}

/// Scalar counterexamples carry a concrete witness, so the under-constrained
/// (datatype-bridge) incompleteness guard never masks them: they stay
/// Counterexamples.
#[test]
fn scalar_false_goals_stay_counterexamples() {
    for case in ["scalar_ge1", "scalar_false_eq"] {
        let result = verify(case);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} (scalar false goal with a concrete witness) should be a counterexample, got {result:?}"
        );
    }
}

/// Opaque generic-return body, unrevealed: the projection is unprovable, so it
/// fails closed — Unknown or Counterexample, never a (false) Verified off the
/// hidden body.
#[test]
fn opaque_generic_return_is_never_falsely_verified() {
    let result = verify("opaque_unrevealed");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "opaque (unrevealed) generic-return projection must not verify off the hidden body, got {result:?}"
    );
}
