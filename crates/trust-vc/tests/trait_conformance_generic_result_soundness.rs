// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Adversarial regression guards for the trait-impl conformance check when the
//! verified function does NOT itself reference the impl method (so no body axiom
//! is otherwise in scope).
//!
//! Pre-fix, the conformance obligation bound `__trust_vc_impl_result` to an
//! unconstrained `concrete_fn(..)` UF and over-rejected a CONFORMING impl with a
//! `@Poly`-valued counterexample (e.g. a generic/inherited-result impl). The fix
//! (`c0158f71`) binds the result to the impl body's ACTUAL captured single-return
//! value, so a conforming impl verifies WITHOUT letting a NON-conforming impl
//! pass.
//!
//! ATTRIBUTION (`a21bf875`): conformance is an ADDRESSABLE per-impl obligation,
//! NOT folded into every function's verdict. A generic trait-bound CALLER whose
//! own contract is trivially true therefore VERIFIES even when a sibling impl in
//! the file is non-conforming — the non-conformance is reported by that impl's
//! OWN conformance obligation (which `cargo trust-vc check` enumerates and fails
//! on), not by sinking the bystander caller. So these guards pin BOTH: the
//! caller is not spuriously sunk, AND the decisive soundness direction — the
//! impl's conformance obligation Counterexamples when (and only when) its body
//! violates the trait contract. (Mirrors `conformance_attribution_soundness.rs`.)

use std::path::PathBuf;
use trust_vc_core::{
    list_trait_conformance_obligations, verify_function_from_file,
    verify_trait_conformance_obligation, VerifyResult,
};

/// Writes `source` to a uniquely-named temp file and returns its path. The name
/// embeds the case label and process id so parallel test threads never collide.
fn write_fixture(label: &str, source: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_conf_generic_{label}_{}.rs",
        std::process::id()
    ));
    std::fs::write(&path, source).expect("write conformance fixture");
    path
}

/// The file's single trait-impl conformance obligation, verified.
fn conformance_verdict(label: &str, source: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("fixture path utf-8");
    let names = list_trait_conformance_obligations(path_str)
        .unwrap_or_else(|err| panic!("{label}: conformance obligations should enumerate: {err}"));
    let name = names
        .into_iter()
        .next()
        .unwrap_or_else(|| panic!("{label}: fixture should declare one conformance obligation"));
    let result = verify_trait_conformance_obligation(path_str, &name).unwrap_or_else(|err| {
        VerifyResult::Error {
            message: err.to_string(),
        }
    });
    let _ = std::fs::remove_file(&path);
    result
}

/// The unrelated generic caller's OWN verdict (must stay Verified — a21bf875:
/// a non-conforming sibling impl does NOT sink an unrelated bystander).
fn caller_verdict(label: &str, source: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result =
        verify_function_from_file(path_str, "unrelated_generic_caller").unwrap_or_else(|err| {
            VerifyResult::Error {
                message: err.to_string(),
            }
        });
    let _ = std::fs::remove_file(&path);
    result
}

/// Strongest guard: a contract-violating impl's OWN obligation must
/// COUNTEREXAMPLE (proving the body actually reached the solver with a model).
/// Used for arithmetic contracts, which the solver refutes definitively. An
/// `Error` would mean the obligation stopped being CHECKED, hollowing the guard.
fn assert_refuted(label: &str, result: VerifyResult) {
    match result {
        VerifyResult::Counterexample { .. } => {}
        VerifyResult::Verified => panic!(
            "{label}: CARDINAL FALSE-VERIFY — a contract-violating impl's own conformance \
             obligation reported Verified; the impl was never checked."
        ),
        other => panic!(
            "{label}: expected a conformance Counterexample (impl body reached the solver), \
             got {other:?}"
        ),
    }
}

/// Gate-faithful rejection guard: a contract-violating impl's obligation must NOT
/// be certified. The decisive property (matching how `cargo trust-vc check`
/// treats it) is `not Verified` — a `Counterexample` (definitive model) OR an
/// `Unknown` (the gate converts a non-discharged conformance obligation to a
/// failure: "not discharged (solver incompleteness)"). A `bool` `returns`/
/// `ensures(result)` obligation over a `@Poly` self currently hits an ay
/// E-matching completeness limit and returns `Unknown` rather than a model — that
/// is FAIL-CLOSED (the gate still rejects the file), NOT a false-verify. `Error`
/// (obligation never reached the solver) and `Verified` (false-verify) both fail.
fn assert_rejected(label: &str, result: VerifyResult) {
    match result {
        VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => panic!(
            "{label}: CARDINAL FALSE-VERIFY — a contract-violating impl's own conformance \
             obligation reported Verified; the impl was never checked."
        ),
        other => panic!(
            "{label}: expected the obligation to be rejected (Counterexample or fail-closed \
             Unknown), got {other:?} — an Error means the body never reached the solver."
        ),
    }
}

fn assert_verified(label: &str, result: VerifyResult) {
    assert!(
        matches!(result, VerifyResult::Verified),
        "{label}: a conforming impl's conformance obligation must Verify, got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// (a) CONFORMING impls: the obligation VERIFIES even though the verified caller
// never references the impl method (no body axiom in scope) — the over-rejection
// `c0158f71` closes. The caller also verifies (it is never sunk).
// ---------------------------------------------------------------------------

const CONFORMING_INHERITED_RETURNS: &str = r#"
#[trust_vc::trait_spec]
trait InheritedReturnsTrue {
    #[trust_vc::returns(true)]
    fn inherited_value(&self) -> bool;
}
struct GoodImpl;
#[trust_vc::trait_impl]
impl InheritedReturnsTrue for GoodImpl {
    fn inherited_value(&self) -> bool {
        true
    }
}
#[trust_vc::ensures(true)]
fn unrelated_generic_caller<T: InheritedReturnsTrue>(value: T) {
    let _ = value.inherited_value();
}
"#;

const CONFORMING_INHERITED_ARITH_ENSURES: &str = r#"
#[trust_vc::trait_spec]
trait ArithEnsures {
    #[trust_vc::ensures(result >= 10)]
    fn arith_value(&self) -> u8;
}
struct GoodArithImpl;
#[trust_vc::trait_impl]
impl ArithEnsures for GoodArithImpl {
    fn arith_value(&self) -> u8 {
        15
    }
}
#[trust_vc::ensures(true)]
fn unrelated_generic_caller<T: ArithEnsures>(value: T) {
    let _ = value.arith_value();
}
"#;

#[test]
fn conforming_inherited_returns_obligation_verifies() {
    assert_verified(
        "conf_returns",
        conformance_verdict("conf_returns", CONFORMING_INHERITED_RETURNS),
    );
}

#[test]
fn conforming_inherited_arith_ensures_obligation_verifies() {
    assert_verified(
        "conf_arith",
        conformance_verdict("conf_arith", CONFORMING_INHERITED_ARITH_ENSURES),
    );
}

#[test]
fn conforming_caller_is_not_sunk() {
    assert!(
        matches!(
            caller_verdict("conf_returns_caller", CONFORMING_INHERITED_RETURNS),
            VerifyResult::Verified
        ),
        "an unrelated generic caller over a conforming impl must verify"
    );
}

// ---------------------------------------------------------------------------
// (b) NON-CONFORMING impls: the impl's OWN obligation Counterexamples (the
// decisive soundness direction — a body that violates the trait contract must be
// refuted). The bystander caller is NOT sunk (attribution, a21bf875); the gate
// rejects the file via the failing conformance obligation.
// ---------------------------------------------------------------------------

const NONCONFORMING_INHERITED_RETURNS: &str = r#"
#[trust_vc::trait_spec]
trait InheritedReturnsTrue {
    #[trust_vc::returns(true)]
    fn inherited_value(&self) -> bool;
}
struct BadImpl;
#[trust_vc::trait_impl]
impl InheritedReturnsTrue for BadImpl {
    fn inherited_value(&self) -> bool {
        false
    }
}
#[trust_vc::ensures(true)]
fn unrelated_generic_caller<T: InheritedReturnsTrue>(value: T) {
    let _ = value.inherited_value();
}
"#;

const NONCONFORMING_INHERITED_ENSURES: &str = r#"
#[trust_vc::trait_spec]
trait EnsuresResult {
    #[trust_vc::ensures(result)]
    fn ensures_value(&self) -> bool;
}
struct BadEnsuresImpl;
#[trust_vc::trait_impl]
impl EnsuresResult for BadEnsuresImpl {
    fn ensures_value(&self) -> bool {
        false
    }
}
#[trust_vc::ensures(true)]
fn unrelated_generic_caller<T: EnsuresResult>(value: T) {
    let _ = value.ensures_value();
}
"#;

const NONCONFORMING_INHERITED_ARITH: &str = r#"
#[trust_vc::trait_spec]
trait ArithEnsures {
    #[trust_vc::ensures(result >= 10)]
    fn arith_value(&self) -> u8;
}
struct BadArithImpl;
#[trust_vc::trait_impl]
impl ArithEnsures for BadArithImpl {
    fn arith_value(&self) -> u8 {
        5
    }
}
#[trust_vc::ensures(true)]
fn unrelated_generic_caller<T: ArithEnsures>(value: T) {
    let _ = value.arith_value();
}
"#;

#[test]
fn nonconforming_inherited_returns_obligation_is_rejected() {
    // bool `returns(true)` over @Poly self → fail-closed (Counterexample or the
    // @Poly-bool E-matching Unknown, both rejected at the gate). Never Verified.
    assert_rejected(
        "bad_returns",
        conformance_verdict("bad_returns", NONCONFORMING_INHERITED_RETURNS),
    );
}

#[test]
fn nonconforming_inherited_ensures_obligation_is_rejected() {
    assert_rejected(
        "bad_ensures",
        conformance_verdict("bad_ensures", NONCONFORMING_INHERITED_ENSURES),
    );
}

#[test]
fn nonconforming_inherited_arith_ensures_obligation_is_refuted() {
    // Arithmetic contract: the solver refutes with a definitive model (5 < 10).
    assert_refuted(
        "bad_arith",
        conformance_verdict("bad_arith", NONCONFORMING_INHERITED_ARITH),
    );
}
