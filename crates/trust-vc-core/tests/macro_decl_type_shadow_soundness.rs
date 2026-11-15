// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! RESIDUAL B of `a10aea13`: "a macro that declares a type is invisible to this
//! walk". Probed on that tree and found EXPLOITABLE and CARDINAL — this file is
//! the guard for the refusal that closes it.
//!
//! The defect: the scope walk answers a bare type name by stepping outward from
//! the use site's module. An item-macro INVOCATION can bind a type in a module
//! the walk passes through, and no walk over the unexpanded AST can see it, so
//! the walk steps past the real declaration and answers with an outer one. That
//! is a confident WRONG shape, not a decline.
//!
//! It cannot be RESOLVED — the expansion is not in the AST — so the shape is
//! REFUSED, narrowly: see `reject_macro_shadowable_type_resolution`. The pins in
//! the second half are what keep that from becoming "reject any file with a
//! macro in it". A macro that emits an impl or a trait, or declares a name the
//! file already binds, is a separate hazard, refused file-wide by the
//! unread-item rule; the pins whose macros declare only a fresh struct or
//! function show the scope refusal's own reach.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx(n: &str) -> String {
    format!("{}/tests/data/{n}", env!("CARGO_MANIFEST_DIR"))
}

const SHADOW: &str = "macro_decl_type_shadow_soundness.rs";
const ORDER_FLIP: &str = "macro_decl_type_shadow_order_flip.rs";
const NARROW: &str = "macro_decl_type_shadow_narrowness.rs";
const LOCAL: &str = "macro_decl_type_shadow_local.rs";

// ---- CARDINAL: the false claim must not verify, in either registry ----

/// Before the fix: `verified`. `rustc` prints `inner S::x = 18446744073709551615`
/// for this exact file, so `s.x <= 255` is false.
#[test]
fn macro_declared_type_must_not_verify() {
    let v = verify_function_from_file(&fx(SHADOW), "macro_decl_shadow_must_not_verify");
    eprintln!("[RESB] macro_decl_shadow_must_not_verify => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: a macro-declared `inner::S` (u64) was answered with the \
         top-level `S`'s u8 shape; got {v:?}"
    );
}

/// Order-independent, unlike the visible-collision family: the macro-declared
/// type is invisible either way, so the one visible declaration answers.
#[test]
fn macro_declared_type_must_not_verify_in_either_order() {
    let v = verify_function_from_file(&fx(ORDER_FLIP), "macro_decl_shadow_must_not_verify");
    eprintln!("[RESB-FLIP] macro_decl_shadow_must_not_verify => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: declaration order must not decide soundness; got {v:?}"
    );
}

/// The METHOD registry, keyed by the receiver type's bare name, was exposed by
/// the same hole: `rustc` prints `inner S::v=2`, and this claims 1.
#[test]
fn macro_declared_method_must_not_verify() {
    let v = verify_function_from_file(&fx(SHADOW), "macro_decl_method_must_not_verify");
    eprintln!("[RESB-METHOD] macro_decl_method_must_not_verify => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: a macro-declared `impl S` was answered by the top-level \
         `impl S`; got {v:?}"
    );
}

// ---- The OTHER direction of the same defect ----
//
// Sub-shape (b)'s signature is that the false claim verifies and the TRUE claim
// is refuted simultaneously, against the same wrong shape. Both of these were
// rejected against the top-level `u8` sort before the fix (one on a `BitVec 64`
// sort mismatch, one with a counterexample model `(S_S #x00)`). They must not
// verify-by-accident either, so what is pinned is that they no longer answer
// against a shape the use site does not name.

#[test]
fn true_claim_is_not_answered_against_the_wrong_shape() {
    let v = verify_function_from_file(&fx(SHADOW), "macro_decl_wide_construct_is_true");
    eprintln!("[RESB-TRUE] macro_decl_wide_construct_is_true => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Counterexample { .. })),
        "a TRUE claim about the macro-declared `u64` field must not be REFUTED \
         against the top-level u8 shape; got {v:?}"
    );
}

#[test]
fn true_method_claim_is_not_refuted_against_the_wrong_shape() {
    let v = verify_function_from_file(&fx(SHADOW), "macro_decl_method_true_is_two");
    eprintln!("[RESB-TRUE-METHOD] macro_decl_method_true_is_two => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Counterexample { .. })),
        "a TRUE claim about the macro-declared method must not be REFUTED \
         against the top-level `impl S`; got {v:?}"
    );
}

// ---- NARROWNESS PINS ----
//
// Each one isolates one of the three conditions in
// `SourceTypeScopeIndex::macro_shadowable_binding`. Delete any condition and the
// corresponding pin goes red.

/// A root use site in the SAME FILE as the reproducers. The scope refusal does
/// not reach it (its macro's module is not on the root's walk path), but
/// `decl_s!` also emits an `impl` and redeclares `S`, items this lane does not
/// read, so the file refuses a `Verified` answer for every function: an impl
/// applies crate-wide, whatever module the macro sits in. Conditions 2 and 3
/// stay pinned below, in files whose macros emit no such item.
#[test]
fn use_site_outside_the_macro_module_meets_the_unread_item_refusal() {
    let v = verify_function_from_file(&fx(SHADOW), "top_level_narrow_is_true");
    eprintln!("[RESB-PIN1] top_level_narrow_is_true => {v:?}");
    assert!(
        matches!(&v, Ok(VerifyResult::Error { message })
            if message.starts_with("unread item") && message.contains("`decl_s!`")),
        "the root use site must be refused by the unread-item rule, not by the \
         scope walk; got {v:?}"
    );
}

#[test]
fn use_site_outside_the_macro_module_meets_the_unread_item_refusal_in_either_order() {
    let v = verify_function_from_file(&fx(ORDER_FLIP), "top_level_narrow_is_true");
    eprintln!("[RESB-PIN2] top_level_narrow_is_true (flip) => {v:?}");
    assert!(
        matches!(&v, Ok(VerifyResult::Error { message })
            if message.starts_with("unread item") && message.contains("`decl_s!`")),
        "order must not affect the pin either; got {v:?}"
    );
}

/// Condition 2 again, from the other side: a macro in a SIBLING module is on
/// nobody's path but its own.
#[test]
fn sibling_module_macro_still_verifies() {
    let v = verify_function_from_file(&fx(NARROW), "sibling_macro_still_verifies");
    eprintln!("[RESB-PIN3] sibling_macro_still_verifies => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: a macro in a sibling module cannot bind a name on this \
         use site's outward walk; got {v:?}"
    );
}

#[test]
fn root_use_site_with_a_module_macro_still_verifies() {
    let v = verify_function_from_file(&fx(NARROW), "root_use_site_with_module_macro");
    eprintln!("[RESB-PIN4] root_use_site_with_module_macro => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: got {v:?}"
    );
}

/// Condition 3: nothing is declared outside the macro's module, so the walk
/// never steps past it and there is nothing an expansion could shadow. Drop
/// this condition and every module that invokes a macro loses its own types.
#[test]
fn local_type_beside_a_macro_still_verifies() {
    let v = verify_function_from_file(&fx(LOCAL), "local_type_beside_macro_verifies");
    eprintln!("[RESB-PIN5] local_type_beside_macro_verifies => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: a type declared in the same module as the invocation \
         has no outer declaration to be confused with; got {v:?}"
    );
}
