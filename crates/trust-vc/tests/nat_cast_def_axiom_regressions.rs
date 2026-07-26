// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression guards for the `nat_to_real` definitional-axiom firing on a
//! cast-wrapped argument.
//!
//! Background: an `open spec fn nat_to_real(n: nat) -> real { n as real }` is
//! encoded as an uninterpreted function plus the definitional axiom
//! `forall n #[trigger nat_to_real(n)]. nat_to_real(n) == n as real`. When the
//! argument is `(x.floor() as nat) + 1`, the Real→Nat cast lowers to an `ite`
//! over a fresh floor skolem and a fresh `__trust_vc_invalid_nat_cast` skolem.
//!
//! Two soundness-preserving engine fixes make the existential discharge:
//!   1. Real→Nat (and the sibling fail-closed nat casts) are memoized on their
//!      source term within a query, so a ground `nat_to_real(cast)` and the
//!      definitional-axiom instance `cast as real` share the *same* argument
//!      term and connect via E-matching (`cast.rs`).
//!   2. The Real→Nat subset guard is emitted as two implications rather than a
//!      single `ite`, so under `x >= 0` the solver derives `result == floor`
//!      by modus ponens instead of a buried case split (`cast.rs`).
//!   3. A triggerless `exists` infers a trigger from its body so the negation
//!      `forall n. !body(n)` carries an E-matching pattern (`refutation.rs`).
//!
//! These tests gate the new positive verdicts and, crucially, the fail-closed
//! negatives that prove the fixes did not weaken soundness.

use std::fs;
use std::path::{Path, PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn write_case(name: &str, code: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("nat_cast_def_axiom");
    fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join(format!("{name}.rs"));
    fs::write(&file, code).expect("write temp source");
    file
}

const NAT_TO_REAL: &str = r#"
pub open spec fn nat_to_real(n: nat) -> real {
    n as real
}
"#;

fn verify(name: &str, code: &str, func: &str) -> VerifyResult {
    let path = write_case(name, code);
    verify_function_from_file(path.to_str().unwrap(), func)
        .unwrap_or_else(|err| panic!("{func} should extract: {err}"))
}

/// The targeted probe: the definitional axiom must fire on the cast-wrapped
/// argument so the equality is trivially provable.
#[test]
fn nat_to_real_def_axiom_fires_on_cast_argument() {
    let code = format!(
        "{NAT_TO_REAL}
#[trust_vc::ensures(true)]
#[trust_vc::requires(x >= 0)]
fn probe(x: real) {{
    let a: nat = x.floor() as nat;
    trust_vc::assert!(nat_to_real(a + 1) == ((a + 1) as real));
}}"
    );
    let result = verify("def_axiom_probe", &code, "probe");
    assert!(
        matches!(result, VerifyResult::Verified),
        "nat_to_real(cast) == cast as real must verify, got: {result:?}"
    );
}

/// The proof-body assert that supplies the existential witness.
#[test]
fn nat_to_real_floor_upper_bound_verifies() {
    let code = format!(
        "{NAT_TO_REAL}
#[trust_vc::ensures(true)]
#[trust_vc::requires(x >= 0)]
fn probe(x: real) {{
    let a: nat = x.floor() as nat;
    trust_vc::assert!(x < nat_to_real(a + 1));
}}"
    );
    let result = verify("floor_upper_bound", &code, "probe");
    assert!(
        matches!(result, VerifyResult::Verified),
        "x < nat_to_real(floor + 1) must verify, got: {result:?}"
    );
}

/// The full upstream `archimedean_nat`: a triggerless existential postcondition
/// discharged by the body witness through the re-applied trigger inference.
#[test]
fn archimedean_nat_existential_discharges() {
    let code = format!(
        "{NAT_TO_REAL}
#[trust_vc::ensures(exists |n: nat| nat_to_real(n) >= x)]
#[trust_vc::requires(x >= 0)]
fn archimedean_nat(x: real) {{
    let a: nat = x.floor() as nat;
    trust_vc::assert!(x < nat_to_real(a + 1));
}}"
    );
    let result = verify("archimedean_nat", &code, "archimedean_nat");
    assert!(
        matches!(result, VerifyResult::Verified),
        "archimedean_nat existential must discharge, got: {result:?}"
    );
}

/// SOUNDNESS: floor-too-low stays a counterexample. `x < a as real` is false
/// whenever the source is non-integer (floor strictly below x), e.g. x = 0.5.
#[test]
fn floor_too_low_stays_counterexample() {
    let code = "
#[trust_vc::ensures(true)]
#[trust_vc::requires(x >= 0)]
fn floor_too_low(x: real) {
    let a: nat = x.floor() as nat;
    trust_vc::assert!(x < (a as real));
}";
    let result = verify("floor_too_low", code, "floor_too_low");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "floor-too-low must stay a counterexample, got: {result:?}"
    );
}

/// SOUNDNESS: without the `x >= 0` precondition the Real→Nat result is
/// unconstrained, so the body assert must NOT verify (fail-closed). The
/// implication-form guard must not leak `result == floor` when `x < 0` is
/// possible.
#[test]
fn missing_precondition_does_not_verify() {
    let code = format!(
        "{NAT_TO_REAL}
#[trust_vc::ensures(true)]
fn probe(x: real) {{
    let a: nat = x.floor() as nat;
    trust_vc::assert!(x < nat_to_real(a + 1));
}}"
    );
    let result = verify("missing_precondition", &code, "probe");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "must fail closed without x >= 0, got: {result:?}"
    );
}
