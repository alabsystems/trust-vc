// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end guards for the Verus `=~=` extensional-equality operator.
//!
//! `=~=` is rewritten at the token level (in `chained_comparisons`) into the
//! existing `ext_eq!` surface, which the encoder expands into the true
//! extensional formula (set membership / map key+value / sequence length+index).
//! These tests run the *full* parse -> lower -> encode -> solve pipeline via
//! `verify_function_from_file`, so a regression in the operator rewrite or its
//! lowering shows up as a wrong verdict, not just a structural mismatch.
//!
//! The adversarial pairs are constructed in *different* orders, so a `Verified`
//! verdict genuinely exercises extensionality (insert order is irrelevant), and
//! a structurally-distinct-but-extensionally-UNEQUAL pair must fail closed:
//! never a false `Verified`.

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    let dir = Path::new("target/ext_eq_operator_roundtrip");
    fs::create_dir_all(dir).unwrap();
    let f = dir.join(format!("{name}.rs"));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

/// (a) Two sets built by inserting the SAME elements in OPPOSITE order are
/// extensionally equal, so `s =~= t` must VERIFY. This is the property the
/// operator exists for: `{0,1} =~= {1,0}` despite a different construction.
#[test]
fn ext_eq_operator_equal_sets_verifies() {
    let code = r#"
#[trust_vc::ensures(true)]
fn ext_eq_set_equal() {
    trust_vc::assert!(
        Set::<u8>::empty().insert(0u8).insert(1u8)
            =~= Set::<u8>::empty().insert(1u8).insert(0u8)
    );
}
"#;
    let r = verify(code, "ext_eq_set_equal");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "extensionally-equal sets must verify under `=~=`, got {:?}",
        r
    );
}

/// (b) SOUNDNESS / fail-closed: a set with an extra element is NOT extensionally
/// equal, so `{0,1} =~= {0}` must NOT verify. A false extensional claim must
/// never produce `Verified`.
#[test]
fn ext_eq_operator_unequal_sets_does_not_verify() {
    let code = r#"
#[trust_vc::ensures(true)]
fn ext_eq_set_unequal() {
    trust_vc::assert!(
        Set::<u8>::empty().insert(0u8).insert(1u8)
            =~= Set::<u8>::empty().insert(0u8)
    );
}
"#;
    let r = verify(code, "ext_eq_set_unequal");
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "extensionally-UNEQUAL sets must NOT verify under `=~=` (fail closed), got {:?}",
        r
    );
}

/// (a) Maps built by inserting the same key/value pairs in opposite order are
/// extensionally equal, so `m =~= n` must VERIFY.
#[test]
fn ext_eq_operator_equal_maps_verifies() {
    let code = r#"
#[trust_vc::ensures(true)]
fn ext_eq_map_equal() {
    trust_vc::assert!(
        Map::<u8, bool>::empty().insert(0u8, true).insert(1u8, false)
            =~= Map::<u8, bool>::empty().insert(1u8, false).insert(0u8, true)
    );
}
"#;
    let r = verify(code, "ext_eq_map_equal");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "extensionally-equal maps must verify under `=~=`, got {:?}",
        r
    );
}

/// (b) SOUNDNESS / fail-closed: maps that agree on keys but DISAGREE on a value
/// are not extensionally equal, so `=~=` must NOT verify.
#[test]
fn ext_eq_operator_unequal_maps_does_not_verify() {
    let code = r#"
#[trust_vc::ensures(true)]
fn ext_eq_map_unequal() {
    trust_vc::assert!(
        Map::<u8, bool>::empty().insert(0u8, true).insert(1u8, false)
            =~= Map::<u8, bool>::empty().insert(0u8, true).insert(1u8, true)
    );
}
"#;
    let r = verify(code, "ext_eq_map_unequal");
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "maps disagreeing on a value must NOT verify under `=~=` (fail closed), got {:?}",
        r
    );
}

/// Cross-check that the `=~=` operator and the explicit `ext_eq!` macro reach
/// the SAME extensional encoder: the equal-set case verifies through both
/// surfaces. (The macro form is the already-tested baseline from `ext_equal.rs`.)
#[test]
fn ext_eq_operator_matches_explicit_macro_for_equal_sets() {
    let code = r#"
#[trust_vc::ensures(true)]
fn ext_eq_macro_baseline() {
    trust_vc::assert!(trust_vc::ext_eq!(
        Set::<u8>::empty().insert(0u8).insert(1u8),
        Set::<u8>::empty().insert(1u8).insert(0u8)
    ));
}
"#;
    let r = verify(code, "ext_eq_macro_baseline");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "explicit ext_eq! baseline must verify, got {:?}",
        r
    );
}
