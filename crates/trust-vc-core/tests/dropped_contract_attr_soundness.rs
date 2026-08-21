// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! FV-2 — dropped contract attributes in the file-VC lane.
//!
//! The outer attribute match in `vc_extraction::attr_extract` ran an allowlist
//! (`requires`/`ensures`/`recommends`/`returns`/`contract`) terminated by
//! `_ => {}`. An unrecognized `trust_vc::`-namespaced clause therefore
//! evaporated, taking its postcondition with it — a FALSE `Verified`. Inside
//! `#[contract(..)]` the identical unknown clause was already a hard error, so
//! the two paths disagreed; the only floor, `ValidationError::OnlyAssumptions`,
//! is per-CONTEXT and cannot see a dropped clause sitting next to a live one.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx() -> String {
    format!(
        "{}/tests/data/dropped_contract_attr_soundness.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

// --- The false-verifies: must NOT report Verified ---------------------------

#[test]
fn ghost_ensures_must_not_be_silently_dropped() {
    let v = verify_function_from_file(&fx(), "ghost_ensures_must_not_be_dropped");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: `#[trust_vc::ghost_ensures(..)]` dropped, got {v:?}"
    );
}

#[test]
fn unknown_trust_vc_segment_must_not_be_silently_dropped() {
    let v = verify_function_from_file(&fx(), "unknown_segment_must_not_be_dropped");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: `#[trust_vc::ensurez(..)]` dropped, got {v:?}"
    );
}

/// The `masked` variant: the dropped clause sits beside a surviving
/// `#[ensures(true)]`, so the `OnlyAssumptions` emptiness guard is satisfied
/// and cannot catch it. This is the case that proves the fix has to live at the
/// attribute-extraction site, not in the validator.
#[test]
fn masked_dropped_clause_must_not_verify() {
    let v = verify_function_from_file(&fx(), "masked_dropped_clause_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: dropped clause masked by a sibling `ensures`, got {v:?}"
    );
}

// --- Narrowness pins: these MUST still verify -------------------------------

#[test]
fn narrowness_pin_correct_clause_still_verifies() {
    let v = verify_function_from_file(&fx(), "correct_clause_still_verifies");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "over-rejection: a correctly spelled `ensures` must still verify, got {v:?}"
    );
}

#[test]
fn narrowness_pin_foreign_attributes_still_ignored() {
    let v = verify_function_from_file(&fx(), "foreign_attributes_still_ignored");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "over-rejection: non-`trust_vc::` attributes (#[inline], #[allow], \
         #[cfg_attr], doc comments) must stay silently ignored, got {v:?}"
    );
}

#[test]
fn narrowness_pin_known_other_trust_vc_attribute_still_verifies() {
    let v = verify_function_from_file(&fx(), "known_other_trust_vc_attribute_still_verifies");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "over-rejection: a KNOWN trust_vc attribute consumed by another pass \
         must not be rejected here, got {v:?}"
    );
}
