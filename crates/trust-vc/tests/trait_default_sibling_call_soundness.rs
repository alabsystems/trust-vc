// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Adversarial regression guards for the round-3 trait surface hole: a
//! non-conforming trait DEFAULT method whose default body calls an UNBOUND
//! sibling trait DEFAULT method in an all-defaults `#[trait_impl]`.
//!
//! Pre-fix, `self.g()` in the default body of `f` could not be lowered onto the
//! concrete conformance surface (the all-defaults impl registered no methods),
//! so the conformance check was SILENTLY SKIPPED while `register_trait` still
//! published the global trait postcondition axiom `forall self. T__f(self) >=
//! 10`. The fix (`2135dde`) inlines the non-overridden sibling's default body
//! (its actual behavior in an all-defaults impl) before lowering, so a
//! non-conforming default Counterexamples and a conforming one still Verifies.
//!
//! ATTRIBUTION (`a21bf875`): conformance is an ADDRESSABLE per-impl obligation,
//! NOT folded into every function's verdict. So the decisive soundness direction
//! is pinned on the impl's OWN conformance obligation (`trait impl conformance
//! Promise::f for S`), which `cargo trust-vc check` enumerates and fails on — NOT
//! on the bystander generic caller, which now correctly VERIFIES by trusting the
//! trait's published contract (exactly as Verus does; the violation is reported
//! against the impl, and the FILE still fails via that obligation). This mirrors
//! the de-stale of `trait_conformance_generic_result_soundness.rs` (`245bfe7`)
//! and `conformance_attribution_soundness.rs`.
//!
//! Each case lives in its own source file because the conformance pass checks
//! EVERY impl in the file — a single non-conforming impl must sink any function
//! whose verification triggers trait registration.

use std::path::PathBuf;
use trust_vc_core::{
    list_trait_conformance_obligations, verify_function_from_file,
    verify_trait_conformance_obligation, VerifyResult,
};

fn write_fixture(label: &str, source: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "trust_vc_trait_sibling_{label}_{}.rs",
        std::process::id()
    ));
    std::fs::write(&path, source).expect("write sibling-call fixture");
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

/// The generic caller's OWN verdict. Post-attribution it must stay Verified — a
/// non-conforming sibling impl does NOT sink an unrelated bystander; it soundly
/// trusts the trait's published contract.
fn caller_verdict(label: &str, source: &str) -> VerifyResult {
    let path = write_fixture(label, source);
    let path_str = path.to_str().expect("fixture path utf-8");
    let result = verify_function_from_file(path_str, "generic_caller_asserts_f_ge_10")
        .unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        });
    let _ = std::fs::remove_file(&path);
    result
}

// ---------------------------------------------------------------------------
// (a) DECISIVE soundness direction: an all-defaults impl whose default `f` calls
// an unbound sibling `g` (default 5) that violates `f`'s ensures (`>= 10`) must
// be REFUTED by its own conformance obligation — a genuine Counterexample (the
// inlined sibling default reaches the solver with the model `f == g == 5`), not
// a fail-closed Error/Unknown.
// ---------------------------------------------------------------------------

// Suffixed literals (`5u8`/`20u8`) keep the MAIN encoding's default-body axiom
// in u8 width; an unsuffixed `5`/`20` is inferred 32-bit and the pre-existing
// `assert_default_body_axiom` lowering fails closed with a sort mismatch (a
// separate, sound fail-closed Error, not part of this soundness cluster).
const BAD_SIBLING_CALL_DEFAULT: &str = r#"
#[trust_vc::trait_spec]
trait Promise {
    fn g(&self) -> u8 {
        5u8
    }
    #[trust_vc::ensures(result >= 10)]
    fn f(&self) -> u8 {
        self.g()
    }
}
struct S;
#[trust_vc::trait_impl]
impl Promise for S {}
#[trust_vc::ensures(true)]
fn generic_caller_asserts_f_ge_10<A: Promise>(a: A) {
    trust_vc::assert!(a.f() >= 10);
}
"#;

#[test]
fn bad_sibling_call_default_conformance_obligation_is_refuted() {
    let result = conformance_verdict("bad", BAD_SIBLING_CALL_DEFAULT);
    // The impl's OWN obligation must COUNTEREXAMPLE (the inlined sibling default
    // `f == g == 5` reached the solver and violates `>= 10`). A `Verified` here
    // is the cardinal false-verify this guard exists to catch; an `Error`/
    // `Unknown` would mean the default body never reached the solver.
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "the conformance obligation for the all-defaults impl whose default `f` returns 5 \
         (via an unbound sibling `g`) must Counterexample — it is a genuinely non-conforming \
         body; got: {result:?}"
    );
}

/// ATTRIBUTION: the bystander generic caller is NOT sunk — it soundly trusts the
/// trait's published `f >= 10` contract and Verifies. The FILE still fails via
/// the conformance obligation above; the caller is not the reporting site.
#[test]
fn bad_sibling_call_default_does_not_sink_bystander_caller() {
    let result = caller_verdict("bad_caller", BAD_SIBLING_CALL_DEFAULT);
    assert!(
        matches!(result, VerifyResult::Verified),
        "post-attribution the generic caller trusts the trait contract and must Verify (the \
         non-conformance is reported against the impl's obligation, not by sinking the \
         caller); got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// (b) NO over-rejection: a CONFORMING all-defaults impl (`g` returns 20, so `f
// >= 10` genuinely holds) — its conformance obligation VERIFIES and the caller
// verifies.
// ---------------------------------------------------------------------------

const GOOD_SIBLING_CALL_DEFAULT: &str = r#"
#[trust_vc::trait_spec]
trait Promise {
    fn g(&self) -> u8 {
        20u8
    }
    #[trust_vc::ensures(result >= 10)]
    fn f(&self) -> u8 {
        self.g()
    }
}
struct S;
#[trust_vc::trait_impl]
impl Promise for S {}
#[trust_vc::ensures(true)]
fn generic_caller_asserts_f_ge_10<A: Promise>(a: A) {
    trust_vc::assert!(a.f() >= 10);
}
"#;

#[test]
fn good_sibling_call_default_conformance_obligation_verifies() {
    let result = conformance_verdict("good", GOOD_SIBLING_CALL_DEFAULT);
    assert!(
        matches!(result, VerifyResult::Verified),
        "a conforming default `f` that calls a sibling default `g` (returning 20, so `f >= \
         10` genuinely holds) — its conformance obligation must Verify, no over-rejection; \
         got: {result:?}"
    );
}

#[test]
fn good_sibling_call_default_caller_verifies() {
    let result = caller_verdict("good_caller", GOOD_SIBLING_CALL_DEFAULT);
    assert!(
        matches!(result, VerifyResult::Verified),
        "a conforming default `f` (>= 10 holds) — the generic caller asserting `a.f() >= 10` \
         must Verify; got: {result:?}"
    );
}
