// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for file-path `trust_vc::closure!` def-side
//! spec extraction, discharged in an ISOLATED child verification context.
//!
//! A def-side-valid closure spec must VERIFY (through the isolated child VC),
//! while every unsound shape must fail closed (Counterexample or Error) — never
//! Verified:
//!   * a bad ensures the body violates,
//!   * a lying ensures (the assume-leak closure a naive call-site injection
//!     would false-verify — the mandatory def-side check rejects it),
//!   * a closure capturing an outer variable in its spec (mutation-capture),
//!   * a call site that must not trust the closure's ensures / return value.
//!
//! POISON PROBE (the reason the lane was quarantined): a never-called closure
//! with `requires(false)` alongside a parent `assert!(false)`. The closure's own
//! def-side check discharges vacuously (`false ⇒ E` is valid), but the PARENT
//! must still return a Counterexample — `false` NEVER enters the parent's
//! assumption set, because the closure's `R`, `res == BODY`, and `E` are routed
//! to an isolated child context whose vectors are discarded. If `false` leaked
//! into the parent, the parent's `assert!(false)` would false-verify.
//!
//! The closure spec is checked ONLY at the definition; the closure value is
//! never modeled, so call sites, reflection, and captures stay fail-closed. See
//! `vc_extraction/body_extract.rs::emit_closure_def_side_obligation` and
//! `VerificationContext::isolated_closure_child`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/closure_spec_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&repro_path(), func)
        .unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

fn assert_not_verified(func: &str) {
    // Extraction may itself fail closed (capture guard / call-site) — an
    // extraction Error is a sound non-verify, so treat an Err as acceptable too.
    if let Ok(VerifyResult::Verified) = verify_function_from_file(&repro_path(), func) {
        panic!("CLOSURE-SPEC FALSE-VERIFY: `{func}` must not verify")
    }
}

#[test]
fn def_side_valid_verifies() {
    // The isolated child VC discharges `y == 2 ∧ res == y ⊢ res == 2`.
    let v = verdict("def_side_valid_verified");
    assert!(
        matches!(v, VerifyResult::Verified),
        "a def-side-valid closure spec should verify; got {v:?}"
    );
}

#[test]
fn bad_ensures_is_counterexample() {
    // body `y` under `requires(y == 2)` gives `res == 2`, contradicting the
    // ensures `z == 3` ⇒ the child def-side VC Counterexamples, surfaced as the
    // function's verdict.
    let v = verdict("def_side_bad_ensures_counterexample");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "a def-side-invalid ensures should Counterexample; got {v:?}"
    );
}

#[test]
fn lying_ensures_is_rejected() {
    // The assume-leak closure: `requires(true)`, body `y` (arbitrary), ensures
    // `z == 100`. The def-side check must reject the lie.
    assert_not_verified("lying_ensures_rejected_counterexample");
}

#[test]
fn captured_variable_fails_closed() {
    assert_not_verified("capture_in_ensures_fail_closed");
}

#[test]
fn call_site_does_not_trust_ensures() {
    // A def-side-valid closure that is then CALLED: the call must not trust the
    // ensures, so `t == 100` must not verify (the closure value is unmodeled).
    assert_not_verified("call_site_does_not_trust_ensures");
}

#[test]
fn requires_false_cannot_poison_parent() {
    // THE POISON PROBE. The closure `requires(false)`; the parent asserts
    // `false`. The closure's own def-side check is vacuously valid, but the
    // parent MUST Counterexample — `false` never entered the parent's
    // assumptions. A parent that VERIFIES here is the cardinal false-verify.
    let v = verdict("requires_false_cannot_poison_parent");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "the parent `assert!(false)` must Counterexample; the closure `requires(false)` \
         must NOT poison the parent context; got {v:?}"
    );
}
