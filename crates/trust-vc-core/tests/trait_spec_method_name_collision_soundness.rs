// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Trait-method contract selection must be keyed by the BOUND, not by the bare
//! method name.
//!
//! This is the trait-contract member of the bare-name-registry class behind the
//! session's cardinal false verifies: a registry keyed by bare name that finds a
//! same-named declaration which is NOT the one the program names, and answers
//! confidently. Two `#[trust_vc::trait_spec]` traits declare
//! `dual_named_method` with conflicting `returns`; the postcondition a call site
//! inherits must come from the trait its type parameter is BOUND by.
//!
//! The behaviour was already correct when these guards were written — what was
//! missing is that nothing VARIED this axis, so no test would have noticed it
//! regressing. Bite-checked: rewriting `supertrait_closure_methods` to ignore
//! its `start` argument and walk every trait declaration in source order (a
//! first-declaration-wins registry) flips
//! `second_bound_false_claim_must_not_verify` to `Verified` and
//! `second_bound_true_claim_verifies` to non-`Verified` in the same build — the
//! diagnostic sub-shape where the false claim is proved and the true one refuted
//! simultaneously. Both directions are therefore pinned below; either alone
//! would miss it.
//!
//! `SpecNine` is declared FIRST, so a bare-name registry still answers the
//! SpecNine-bounded pair correctly. The SECOND-bound pair is the discriminator.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx() -> String {
    format!(
        "{}/tests/data/trait_spec_method_name_collision.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(case: &str) -> Result<VerifyResult, String> {
    verify_function_from_file(&fx(), case).map_err(|err| err.to_string())
}

// ---- SOUNDNESS: a colliding sibling's postcondition must never be inherited ----

#[test]
fn second_bound_must_not_inherit_first_declared_trait_postcondition() {
    let v = verdict("second_bound_false_claim_must_not_verify");
    eprintln!("[TSC-FV] second_bound_false_claim_must_not_verify => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: under `T: SpecTwo` the call inherited SpecNine's \
         `returns(9u8)`; stock rustc returns 2. Contract selection fell back to \
         the bare method name; got {v:?}"
    );
}

#[test]
fn first_bound_must_not_inherit_second_declared_trait_postcondition() {
    let v = verdict("first_bound_false_claim_must_not_verify");
    eprintln!("[TSC-FV2] first_bound_false_claim_must_not_verify => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: under `T: SpecNine` the call inherited SpecTwo's \
         `returns(2u8)`; stock rustc returns 9; got {v:?}"
    );
}

// ---- NARROWNESS PINS: selection must still SUCCEED for the right trait ----
//
// Without these, dropping every colliding key would pass the two guards above
// while silently destroying the capability. The second-bound pin is the load
// bearing one: it is the assertion the bite check breaks.

#[test]
fn second_bound_still_inherits_its_own_postcondition() {
    let v = verdict("second_bound_true_claim_verifies");
    eprintln!("[TSC-PIN1] second_bound_true_claim_verifies => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: `T: SpecTwo` must still inherit SpecTwo's \
         `returns(2u8)` despite the colliding method name; got {v:?}"
    );
}

#[test]
fn first_bound_still_inherits_its_own_postcondition() {
    let v = verdict("first_bound_true_claim_verifies");
    eprintln!("[TSC-PIN2] first_bound_true_claim_verifies => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: `T: SpecNine` must still inherit SpecNine's \
         `returns(9u8)`; got {v:?}"
    );
}

#[test]
fn uncollided_bound_still_inherits_its_postcondition() {
    let v = verdict("sole_bound_true_claim_verifies");
    eprintln!("[TSC-PIN3] sole_bound_true_claim_verifies => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: a method name declared by exactly one trait_spec must \
         still resolve; got {v:?}"
    );
}

/// Guards the pin above against being satisfied vacuously: if the uncollided
/// bound's context were inconsistent, every claim about it would verify.
#[test]
fn uncollided_bound_still_refutes_a_wrong_value() {
    let v = verdict("sole_bound_false_claim_must_not_verify");
    eprintln!("[TSC-PIN4] sole_bound_false_claim_must_not_verify => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "an uncollided trait bound must still refute a false value — a verifying \
         result here means the context proves anything; got {v:?}"
    );
}
