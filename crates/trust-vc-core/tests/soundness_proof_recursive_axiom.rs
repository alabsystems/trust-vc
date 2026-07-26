// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Soundness regression (round-4, proof/exec self-recursion class): a
//! self-recursive `#[trust_vc::proof]` inherent method or free proof fn with a
//! value return and no `#[decreases]` termination measure must never publish a
//! usable single-return body axiom (`m(s,n) == m(s,n) + 1`, i.e. `0 == 1`) that
//! lets a false goal verify vacuously.
//!
//! Sibling of `soundness_recursive_axiom.rs` (the `#[trust_vc::spec]` catalog
//! class). Gate lives in `vc_extraction.rs::self_recursive_body_axiom_unsound`,
//! applied at `InherentMethodDef::from_impl_method` and
//! `SiblingHelperDef::from_item_fn_with_name`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/proof_recursive_axiom_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&repro_path(), func)
        .unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

// ---- The hole: every false goal driven by the ill-founded recursive axiom ----

#[test]
fn self_recursive_proof_method_must_not_prove_false() {
    let v = verdict("exploit_false");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "UNSOUND: assert!(false) verified via an ill-founded self-recursive \
         inherent-method body axiom (no decreases proof). Verdict: {v:?}"
    );
}

#[test]
fn self_recursive_proof_method_must_not_prove_arithmetic_false() {
    let v = verdict("exploit_plus_100");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "UNSOUND: m(3) == m(3) + 100 verified via the recursive method axiom. \
         Verdict: {v:?}"
    );
}

#[test]
fn self_recursive_free_proof_fn_must_not_prove_false() {
    let v = verdict("exploit_free_false");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "UNSOUND: assert!(false) verified via an ill-founded self-recursive free \
         proof-fn (sibling-helper) body axiom. Verdict: {v:?}"
    );
}

#[test]
fn control_false_without_axiom_does_not_verify() {
    // Causation control: the same false goal with no recursive call must also
    // not verify (guards against the soundness assertions passing vacuously).
    let v = verdict("control_false_no_call");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "control: assert!(false) must not verify; got {v:?}"
    );
}

// ---- No over-rejection: legitimate body axioms must STILL verify ----

#[test]
fn non_recursive_inherent_method_axiom_still_verifies() {
    assert!(
        matches!(verdict("pos_inc"), VerifyResult::Verified),
        "OVER-REJECTION: a non-recursive inherent-method body axiom must still \
         prove s.inc(5) == 6"
    );
}

#[test]
fn well_founded_recursive_method_with_decreases_still_verifies() {
    assert!(
        matches!(verdict("pos_cnt_base"), VerifyResult::Verified),
        "OVER-REJECTION: a well-founded recursive method WITH #[decreases] must \
         still prove its base case"
    );
}

#[test]
fn non_recursive_free_helper_axiom_still_verifies() {
    assert!(
        matches!(verdict("pos_g"), VerifyResult::Verified),
        "OVER-REJECTION: a non-recursive free-helper body axiom must still prove \
         g(5) == 6"
    );
}

#[test]
fn well_founded_recursive_free_fn_with_decreases_still_verifies() {
    assert!(
        matches!(verdict("pos_fcnt_base"), VerifyResult::Verified),
        "OVER-REJECTION: a well-founded recursive free fn WITH #[decreases] must \
         still prove its base case"
    );
}

#[test]
fn free_helper_axiom_is_live_false_fact_refuted() {
    // Non-vacuity witness: the positive verdicts are driven by a live body axiom,
    // not a vacuous context — a false fact about g must be refuted.
    let v = verdict("neg_g_false");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "g's body axiom should refute g(5) == 7; got {v:?}"
    );
}
