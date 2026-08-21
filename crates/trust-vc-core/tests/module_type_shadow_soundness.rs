// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! FV-1: the source-type registry keys structs/enums/aliases by BARE identifier
//! and recurses into inline `mod`s, so a nested-module type could silently
//! supply the field types of a same-named top-level type. Narrower-first was a
//! cardinal false-verify; the verdict flipped with declaration order alone.
//!
//! A colliding bare name is now resolved against the USE SITE'S MODULE SCOPE
//! where scope settles it (which is why the two reproducers below both yield a
//! counterexample, in either declaration order, rather than an error), and fails
//! closed where it does not. The boundary between those two lives in
//! `module_type_shadow_resolution.rs`; what this file pins is only that no
//! order, and no map-priority tiebreak, can produce `Verified`.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx(n: &str) -> String {
    format!("{}/tests/data/{n}", env!("CARGO_MANIFEST_DIR"))
}

const SHADOW: &str = "module_type_shadow_soundness.rs";
const ORDER_FLIP: &str = "module_type_shadow_order_flip.rs";

#[test]
fn collided_bare_name_must_not_verify() {
    let v = verify_function_from_file(&fx(SHADOW), "collided_field_width_must_not_verify");
    eprintln!("[FV1] collided_field_width_must_not_verify => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: nested `helper::S` (u8) shadowed the top-level `S` (u64); got {v:?}"
    );
}

#[test]
fn collided_bare_name_must_not_verify_in_either_order() {
    let v = verify_function_from_file(&fx(ORDER_FLIP), "collided_field_width_must_not_verify");
    eprintln!("[FV1-FLIP] collided_field_width_must_not_verify => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: declaration order must not decide soundness; got {v:?}"
    );
}

/// A struct/enum collision on one bare name was once resolved by MAP PRIORITY
/// (`structs` is consulted before `enums`), not by declaration order, so this
/// shape was not itself verifying falsely — but it is the same guess, made on a
/// different tiebreak. Collision handling spans all three registry maps: scope
/// picks the top-level `struct Shape` here and the map-priority tiebreak is
/// never consulted, so `sh.w <= 255` is refuted rather than assumed.
#[test]
fn cross_kind_collision_must_not_verify() {
    let v = verify_function_from_file(&fx(SHADOW), "cross_kind_collision_must_not_verify");
    eprintln!("[FV1-KIND] cross_kind_collision_must_not_verify => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "a struct/enum bare-name collision must decline, not pick by map order; got {v:?}"
    );
}

// ---- NARROWNESS PINS: the fix must not degenerate into blanket rejection ----

#[test]
fn non_colliding_module_type_still_verifies() {
    let v = verify_function_from_file(&fx(SHADOW), "module_type_without_collision_verifies");
    eprintln!("[FV1-PIN1] module_type_without_collision_verifies => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: a nested-module type that collides with nothing must still \
         resolve to its real fields; got {v:?}"
    );
}

#[test]
fn top_level_type_beside_module_types_still_verifies() {
    let v = verify_function_from_file(&fx(SHADOW), "top_level_type_verifies");
    eprintln!("[FV1-PIN2] top_level_type_verifies => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: top-level types must be unaffected by unrelated module \
         types in the same file; got {v:?}"
    );
}

#[test]
fn token_identical_redeclaration_still_verifies() {
    let v = verify_function_from_file(&fx(SHADOW), "identical_redeclaration_still_verifies");
    eprintln!("[FV1-PIN3] identical_redeclaration_still_verifies => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: two token-identical declarations agree on the shape, so \
         resolving them is not a guess; got {v:?}"
    );
}
