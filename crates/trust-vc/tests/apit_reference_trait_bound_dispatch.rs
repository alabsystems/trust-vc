// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Argument-position `impl Trait` BEHIND A REFERENCE (`&impl Tr`,
//! `&mut impl Tr`, `&(impl A + B)`) resolves through the generic-trait-bound
//! dispatch path, exactly as the already-working by-value `impl Tr` does.
//!
//! `fn f(x: &impl Tr)` is Rust sugar for `fn f<A: Tr>(x: &A)`, and BOTH of
//! those spellings are proven to work here in both directions. Before the
//! reference-wrapper widening in `impl_trait_desugar`, only the by-value form
//! desugared: `&impl Tr` kept its `Type::Reference` wrapper, never became a
//! type parameter, and every call on it fail-closed with "unsupported method".
//!
//! LIAR PINS — the point of this file is not that more things verify, it is
//! that nothing FALSE became provable along the way:
//!
//! * `*_liar_*` — claiming MORE than the bounds give must still be REJECTED,
//!   at the exact conjunction boundary (`>= 5` verifies, `>= 6` does not).
//! * `chained_bound_liar_*` — with `T: P1 + P2`, the claim must be discharged
//!   by the CONJUNCTION of both bounds' `ensures`, never by more.
//! * `unbound_trait_fact_does_not_leak` — a trait that is NOT among the
//!   receiver's bounds must contribute nothing, even when it is declared in the
//!   same file and even when it declares a same-named method.
//! * `composite_wrapped_apit_still_fails_closed` — the NARROWNESS pin. Only
//!   `&` / `&mut` / paren wrappers were opened up; `Vec<impl Tr>` and friends
//!   must keep failing closed rather than silently resolving through a
//!   receiver shape that was never measured.

use trust_vc_core::{verify_function_from_file, VerifyResult};

use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

static FIXTURE_SEQ: AtomicUsize = AtomicUsize::new(0);

fn write_fixture(label: &str, source: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_apit_ref_{label}_{}_{}.rs",
        std::process::id(),
        FIXTURE_SEQ.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, source).expect("write APIT fixture");
    path
}

fn verdict(label: &str, source: &str, func: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result =
        verify_function_from_file(path_str, func).unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        });
    let _ = std::fs::remove_file(&path);
    result
}

fn assert_verified(label: &str, source: &str) {
    let result = verdict(label, source, "g");
    assert!(
        matches!(result, VerifyResult::Verified),
        "{label}: a TRUE consequence of the receiver's trait bounds must verify, got: {result:?}"
    );
}

/// A claim that does NOT follow from the bounds must be REFUTED, and refuted
/// for the right reason: only `Counterexample` (the solver found the model) or
/// a fail-closed `Unknown` count.
///
/// `Error` is EXCLUDED on purpose. Every liar pin in this file passed on
/// `Error` in its first run — the fixtures carried an attribute this API path
/// rejects, so nothing reached the solver and the whole file was vacuous while
/// reporting 8 green. A liar pin that cannot tell "refuted" from "never ran" is
/// not a pin.
fn assert_rejected(label: &str, source: &str) {
    let result = verdict(label, source, "g");
    match result {
        VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => panic!(
            "{label}: FALSE-VERIFY — a claim stronger than the trait bounds justify reported \
             Verified. The reference-APIT desugar must never manufacture facts."
        ),
        other => panic!(
            "{label}: expected a genuine refutation (Counterexample or fail-closed Unknown), \
             got {other:?} — an Error means the fixture never reached the solver and this pin \
             proved nothing."
        ),
    }
}

/// The NARROWNESS pin's expected state is different from a liar pin's: an
/// out-of-scope receiver shape is supposed to fail at LOWERING, so `Error` is
/// the correct outcome there and `Verified` is the forbidden one.
fn assert_not_verified(label: &str, source: &str) {
    let result = verdict(label, source, "g");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "{label}: a receiver shape outside the desugar's measured scope must NOT verify, \
         got Verified — the wrapper set was widened without measuring the new shape."
    );
}

/// Two independent single-method traits, used by every fixture below. Bodies
/// are unreachable in verification (only the declared contracts are consumed),
/// so the traits stay contract-only.
const TRAITS: &str = r#"
#[trust_vc::trait_spec]
pub trait P1 {
    #[trust_vc::ensures(result >= 2)]
    fn a(&self) -> int;
}

#[trust_vc::trait_spec]
pub trait P2 {
    #[trust_vc::ensures(result >= 3)]
    fn b(&self) -> int;
}
"#;

fn fixture(signature_and_body: &str) -> String {
    format!("{TRAITS}\n{signature_and_body}\n")
}

// ---------------------------------------------------------------------------
// CAPABILITY: the shapes that fail-closed before the widening.
// ---------------------------------------------------------------------------

#[test]
fn shared_reference_apit_single_bound_verifies() {
    assert_verified(
        "ref_single",
        &fixture(
            r#"
#[trust_vc::ensures(result >= 2)]
pub fn g(t: &impl P1) -> int { t.a() }
"#,
        ),
    );
}

#[test]
fn shared_reference_apit_chained_bounds_conjoin() {
    assert_verified(
        "ref_chained",
        &fixture(
            r#"
#[trust_vc::ensures(result >= 5)]
pub fn g(t: &(impl P1 + P2)) -> int { t.a() + t.b() }
"#,
        ),
    );
}

#[test]
fn mutable_reference_apit_verifies() {
    assert_verified(
        "mut_ref_single",
        &fixture(
            r#"
#[trust_vc::ensures(result >= 2)]
pub fn g(t: &mut impl P1) -> int { t.a() }
"#,
        ),
    );
}

/// The written-out generic spelling `fn g<T: P1 + P2>(t: &T)` is what the
/// desugar targets. Pinning it here keeps the two spellings' verdicts tied
/// together: if this one ever regresses, the desugar's target moved.
#[test]
fn written_generic_reference_bound_still_verifies() {
    assert_verified(
        "written_generic_ref",
        &fixture(
            r#"
#[trust_vc::ensures(result >= 5)]
pub fn g<T: P1 + P2>(t: &T) -> int { t.a() + t.b() }
"#,
        ),
    );
}

/// A DESCRIPTIVELY-NAMED generic behind a reference (`&Item`, not `&T`). This
/// is the second half of the same defect: the declared-type-param lookup ran on
/// the undecorated string only, so a reference-typed generic was recognized by
/// NAME LENGTH — `&T` passed the ≤2-char heuristic, `&Item` fell through to
/// `Opaque` and sank the context.
#[test]
fn long_named_generic_behind_reference_verifies() {
    assert_verified(
        "long_named_generic_ref",
        &fixture(
            r#"
#[trust_vc::ensures(result >= 5)]
pub fn g<Item: P1 + P2>(t: &Item) -> int { t.a() + t.b() }
"#,
        ),
    );
}

// ---------------------------------------------------------------------------
// LIAR PINS (a): claiming MORE than the bounds give must be REJECTED.
// ---------------------------------------------------------------------------

#[test]
fn shared_reference_apit_liar_single_bound_is_rejected() {
    assert_rejected(
        "ref_single_liar",
        &fixture(
            r#"
#[trust_vc::ensures(result >= 3)]
pub fn g(t: &impl P1) -> int { t.a() }
"#,
        ),
    );
}

/// The conjunction boundary itself: `>= 5` verifies above, so `>= 6` — one more
/// than both bounds together justify — must be refused.
#[test]
fn chained_bound_liar_beyond_the_conjunction_is_rejected() {
    assert_rejected(
        "ref_chained_liar",
        &fixture(
            r#"
#[trust_vc::ensures(result >= 6)]
pub fn g(t: &(impl P1 + P2)) -> int { t.a() + t.b() }
"#,
        ),
    );
}

#[test]
fn mutable_reference_apit_liar_is_rejected() {
    assert_rejected(
        "mut_ref_liar",
        &fixture(
            r#"
#[trust_vc::ensures(result >= 3)]
pub fn g(t: &mut impl P1) -> int { t.a() }
"#,
        ),
    );
}

#[test]
fn long_named_generic_behind_reference_liar_is_rejected() {
    assert_rejected(
        "long_named_generic_ref_liar",
        &fixture(
            r#"
#[trust_vc::ensures(result >= 6)]
pub fn g<Item: P1 + P2>(t: &Item) -> int { t.a() + t.b() }
"#,
        ),
    );
}

// ---------------------------------------------------------------------------
// LIAR PINS (b): a fact from a trait that is NOT on the receiver must not leak.
// ---------------------------------------------------------------------------

/// `P2` is declared in the file (so its postcondition axiom is in scope) but is
/// NOT a bound on this receiver. `P1` alone gives `>= 2`; borrowing `P2`'s
/// `>= 3` would be a leak across bounds.
#[test]
fn unbound_trait_fact_does_not_leak_into_a_single_bound_receiver() {
    assert_rejected(
        "unbound_leak",
        &fixture(
            r#"
#[trust_vc::ensures(result >= 3)]
pub fn g(t: &impl P1) -> int { t.a() }
"#,
        ),
    );
}

/// The sharper form: the unbound trait declares a SAME-NAMED method, so a
/// resolver that keyed on the method name alone would pick up the stronger
/// contract. The bound on `t` is `P1`; `Strong::a`'s `>= 100` must not apply.
#[test]
fn same_named_method_on_an_unbound_trait_does_not_leak() {
    assert_rejected(
        "same_named_leak",
        r#"
#[trust_vc::trait_spec]
pub trait P1 {
    #[trust_vc::ensures(result >= 2)]
    fn a(&self) -> int;
}

#[trust_vc::trait_spec]
pub trait Strong {
    #[trust_vc::ensures(result >= 100)]
    fn a(&self) -> int;
}

#[trust_vc::ensures(result >= 100)]
pub fn g(t: &impl P1) -> int { t.a() }
"#,
    );
}

/// Two DIFFERENT receivers, one bound each. `u`'s `P2` bound must not travel to
/// `t`, whose only bound is `P1`.
#[test]
fn a_bound_on_another_parameter_does_not_leak() {
    assert_rejected(
        "cross_param_leak",
        &fixture(
            r#"
#[trust_vc::ensures(result >= 3)]
pub fn g(t: &impl P1, u: &impl P2) -> int { t.a() }
"#,
        ),
    );
}

// ---------------------------------------------------------------------------
// NARROWNESS PIN: only reference/paren wrappers were opened up.
// ---------------------------------------------------------------------------

/// `Vec<impl Tr>` is NOT a reference wrapper. It must keep its existing
/// fail-closed handling — a desugar that reached into arbitrary composites
/// would be normalizing into a receiver shape nobody has measured.
///
/// This asserts non-verification, which is exactly the state before the change;
/// it exists so a future widening of the wrapper set cannot land silently.
#[test]
fn composite_wrapped_apit_still_fails_closed() {
    assert_not_verified(
        "composite_narrowness",
        &fixture(
            r#"
#[trust_vc::ensures(result >= 2)]
pub fn g(t: Vec<impl P1>) -> int { t[0].a() }
"#,
        ),
    );
}
