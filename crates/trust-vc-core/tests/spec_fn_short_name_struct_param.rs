// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! A user struct whose name is 1-2 uppercase letters may be a spec function's
//! parameter type.
//!
//! The flat type-string parser classifies such a name as a generic `TypeParam`
//! by Rust naming convention, and a `TypeParam` erases to the uninterpreted
//! `Poly` sort. That classification happened BEFORE the struct registry was
//! consulted, so `resolve_opaque_leaves` — which already replaced `Opaque` leaves
//! with the registered datatype carrier — never saw the name. The spec fn's body
//! axiom then bound its quantified variable at `Poly` while the verified caller,
//! whose own parameters DO go through the registry, applied the same helper at
//! the concrete carrier, and encoding aborted with
//! `sort mismatch in apply: expected matching domain sort, got Poly`.
//!
//! Every pin below discriminates three ways: `Verified`, `Counterexample` and
//! `Err` are distinct outcomes, so a test can tell "one agreed carrier" from
//! "the wrong carrier" from "declined". The liars matter as much as the truths —
//! the fix only makes two encoding sorts agree, so a liar of the same shape must
//! still be refuted rather than swept into the newly-encodable set.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx(n: &str) -> String {
    format!("{}/tests/data/{n}", env!("CARGO_MANIFEST_DIR"))
}

const SHORT: &str = "spec_fn_short_name_struct_param.rs";
const SHADOWED: &str = "spec_fn_generic_shadowed_by_struct.rs";
const UNSHADOWED: &str = "spec_fn_generic_unshadowed.rs";

// ---- TRUTHS: the capability itself ----------------------------------------

/// `fn inv_short(s: SP) -> bool { s.a > 10 }` used as a `requires` on a caller
/// taking `SP` by value. `a > 10` entails `result > 5`.
#[test]
fn short_name_struct_param_by_value_verifies() {
    let v = verify_function_from_file(&fx(SHORT), "short_name_struct_param_truth");
    eprintln!("[SHORT-VAL] short_name_struct_param_truth => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "a spec fn over a short-named user struct must encode at one agreed \
         carrier, not abort on a Poly sort mismatch; got {v:?}"
    );
}

/// Same, with the spec fn taking `&SP`. The reference form went through the same
/// leaf classification, so it failed the same way.
#[test]
fn short_name_struct_param_by_ref_verifies() {
    let v = verify_function_from_file(&fx(SHORT), "short_name_struct_param_by_ref_truth");
    eprintln!("[SHORT-REF] short_name_struct_param_by_ref_truth => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "the by-reference form must resolve the same carrier as by-value; got {v:?}"
    );
}

/// LONG-NAME CONTROL. `Catalog` was never mistaken for a type parameter, so this
/// path already worked. It fixes the expected verdict for the short-name pins
/// above and catches a fix that damages the pre-existing `Opaque` route.
#[test]
fn long_name_struct_param_still_verifies() {
    let v = verify_function_from_file(&fx(SHORT), "long_name_struct_param_truth");
    eprintln!("[LONG-VAL] long_name_struct_param_truth => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "the already-working long-name path must be untouched; got {v:?}"
    );
}

// ---- LIARS: the soundness half --------------------------------------------
//
// `s.a > 10` on a `u64` gives `a >= 11`, so `result > 11` is false at `a == 11`.
// Each liar differs from its truth only in that bound.

#[test]
fn short_name_struct_param_by_value_liar_is_refuted() {
    let v = verify_function_from_file(&fx(SHORT), "short_name_struct_param_liar");
    eprintln!("[SHORT-VAL-LIAR] short_name_struct_param_liar => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Counterexample { .. })),
        "making the sorts agree must not make an unentailed postcondition \
         provable; `a > 10` does not give `a > 11`. got {v:?}"
    );
}

#[test]
fn short_name_struct_param_by_ref_liar_is_refuted() {
    let v = verify_function_from_file(&fx(SHORT), "short_name_struct_param_by_ref_liar");
    eprintln!("[SHORT-REF-LIAR] short_name_struct_param_by_ref_liar => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Counterexample { .. })),
        "the by-reference liar must be refuted too; got {v:?}"
    );
}

#[test]
fn long_name_struct_param_liar_is_refuted() {
    let v = verify_function_from_file(&fx(SHORT), "long_name_struct_param_liar");
    eprintln!("[LONG-VAL-LIAR] long_name_struct_param_liar => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Counterexample { .. })),
        "the long-name liar must stay refuted; got {v:?}"
    );
}

// ---- FV-1 COLLISION: the fix must not route around the registry -----------

/// Two declarations of `SP` with different field widths. The fix resolves a
/// `TypeParam` leaf against the SAME source-type registry the `Opaque` arm
/// already used, so it must inherit that registry's collision handling rather
/// than reach past it and pick first-declaration-wins — the shape of FV-1.
/// `s.a <= 255` holds only for the `u8` declaration, so `Verified` here would
/// mean a declaration was chosen on no grounds.
#[test]
fn collided_short_name_struct_does_not_verify() {
    let v = verify_function_from_file(
        &fx("spec_fn_short_name_struct_collision.rs"),
        "collided_short_name_must_not_verify",
    );
    eprintln!("[FV1-COLLIDE] collided_short_name_must_not_verify => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "an ambiguous bare type name must not resolve to whichever declaration \
         came first; got {v:?}"
    );
}

// ---- NARROWNESS PIN: a signature's own generic still erases ----------------

/// A struct named `T` must NOT capture a spec fn that declares its own generic
/// `T`. This pin is load-bearing and observable: dropping the
/// `!sig_type_params.contains(&name)` guard monomorphizes `always<T>` to the
/// struct carrier, and this `u64` call site then fails to encode.
#[test]
fn signature_generic_shadows_a_same_named_struct() {
    let v = verify_function_from_file(&fx(SHADOWED), "generic_shadowed_by_struct");
    eprintln!("[PIN-SHADOW] generic_shadowed_by_struct => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "`fn always<T>(x: T)` declares its own `T`, which shadows `struct T`; \
         pinning it to the struct carrier breaks the u64 call site. got {v:?}"
    );
}

/// UNSHADOWED CONTROL: byte-identical but for the absent `struct T`. Comparing
/// the two is what makes the pin above a statement about shadowing rather than
/// about generics in general.
#[test]
fn generic_verdict_is_independent_of_a_same_named_struct() {
    let shadowed = verify_function_from_file(&fx(SHADOWED), "generic_shadowed_by_struct");
    let unshadowed = verify_function_from_file(&fx(UNSHADOWED), "generic_shadowed_by_struct");
    eprintln!("[PIN-CTRL] shadowed => {shadowed:?} / unshadowed => {unshadowed:?}");
    assert!(
        matches!(unshadowed, Ok(VerifyResult::Verified)),
        "control: the generic spec fn verifies with no struct in scope; got {unshadowed:?}"
    );
    assert_eq!(
        format!("{shadowed:?}"),
        format!("{unshadowed:?}"),
        "the presence of a same-named struct must not change a generic \
         parameter's verdict"
    );
}
