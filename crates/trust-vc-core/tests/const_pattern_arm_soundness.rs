// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! A `const`-NAME pattern is REFUTABLE, and treating it as an irrefutable
//! binder was a CARDINAL FALSE VERIFY.
//!
//! ```ignore
//! const K: u64 = 5;
//! match n { K => {} _ => { assert!(false); } }   // VERIFIED
//! match n { 5 => {} _ => { assert!(false); } }   // counterexample
//! ```
//!
//! `arm_pattern_match_condition` classified the `K` arm as `Always` — it is not
//! a datatype variant, so it fell through to the bare-binder answer — which
//! made the wildcard arm's prior-negation `!(true)`, i.e. FALSE, and vacuously
//! discharged every obligation in it.
//!
//! The fix decides by DECLARATION, not by spelling: `const_pattern_desugar`
//! folds a declared const pattern to its literal value before extraction, and
//! `arm_pattern_match_condition` fails closed on a bare ident it cannot rule
//! out as an item reference.
//!
//! Every soundness case here is paired with its LITERAL twin, which is the
//! discriminator that proved the defect: the two spellings are the same Rust
//! program and must reach the same verdict.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx() -> String {
    format!(
        "{}/tests/data/const_pattern_arm_soundness.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(name: &str) -> Result<VerifyResult, trust_vc_core::TrustVcError> {
    let v = verify_function_from_file(&fx(), name);
    eprintln!("[CONSTPAT] {name} => {v:?}");
    v
}

// ---- THE CARDINAL FALSE VERIFY --------------------------------------------

#[test]
fn const_arm_must_not_vacuously_discharge_its_sibling() {
    let v = verdict("const_arm_sibling_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: a `const K` arm made the wildcard arm's guard FALSE, so \
         `assert!(false)` was vacuously discharged; got {v:?}"
    );
}

#[test]
fn lowercase_const_arm_must_not_vacuously_discharge_its_sibling() {
    let v = verdict("lowercase_const_arm_sibling_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: the lowercase spelling of a const pattern is still a \
         const pattern — Rust resolves the ITEM, not the case; got {v:?}"
    );
}

/// THE DISCRIMINATOR. The literal twin always refuted; if it ever stops doing
/// so the paired assertions above prove nothing.
#[test]
fn literal_twin_still_refutes() {
    let v = verdict("literal_arm_sibling_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "the literal control must refute — it is what the const form is compared \
         against; got {v:?}"
    );
}

// ---- LIAR PINS -------------------------------------------------------------
// The const arm now supplies `n == 5`. Proving more is only progress if nothing
// FALSE became provable.

#[test]
fn const_arm_liar_must_not_verify() {
    let v = verdict("const_arm_liar_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "LIAR PIN: the `K` arm supplies `n == 5`, never `n == 6`; got {v:?}"
    );
}

#[test]
fn wildcard_arm_liar_must_not_verify() {
    let v = verdict("wildcard_arm_liar_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "LIAR PIN: the sibling arm is reached only when `n != 5`, so `n == 5` \
         must be refuted there; got {v:?}"
    );
}

#[test]
fn duplicated_const_name_is_not_folded_to_a_value() {
    let v = verdict("duplicated_const_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "LIAR PIN: a name declared twice must not be folded to either value — \
         picking one would be a guess, and the wrong guess is a false verify; \
         got {v:?}"
    );
}

// ---- CAPABILITY ------------------------------------------------------------

#[test]
fn const_arm_supplies_its_value() {
    let v = verdict("const_arm_supplies_its_value");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "CAPABILITY: the selected `K` arm must know `n == 5`; got {v:?}"
    );
}

#[test]
fn wildcard_arm_knows_the_negation() {
    let v = verdict("wildcard_arm_knows_the_negation");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "CAPABILITY: the sibling arm must know `n != 5` — the obligation that \
         used to be vacuous; got {v:?}"
    );
}

// ---- NARROWNESS PINS -------------------------------------------------------

#[test]
fn ordinary_binder_still_binds() {
    let v = verdict("ordinary_binder_still_binds");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: an ordinary lowercase binder naming no declared const \
         must still bind — the overwhelmingly common case; got {v:?}"
    );
}

#[test]
fn ordinary_binder_liar_must_not_verify() {
    let v = verdict("ordinary_binder_liar_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "a binder binds the scrutinee, it does not constrain it; got {v:?}"
    );
}

#[test]
fn binder_colliding_with_an_associated_const_still_binds() {
    let v = verdict("binder_colliding_with_assoc_const_still_binds");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: a bare name never resolves to an ASSOCIATED const \
         (`Holder::assoc_named` is required), so it is still a binder — \
         treating one as a const pattern would narrow the arm's path condition, \
         which is the false-verify direction; got {v:?}"
    );
}
