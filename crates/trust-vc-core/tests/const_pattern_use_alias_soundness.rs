// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! A `use` ALIAS of a `const` is still a `const` pattern — and it bypassed the
//! declaration-keyed registry that closed the direct route. CARDINAL FALSE
//! VERIFY.
//!
//! ```ignore
//! #![allow(non_upper_case_globals)]
//! pub const lower_k: u64 = 5;
//! use crate::lower_k as alias_k;
//!
//! #[trust_vc::requires(n < 100)]
//! pub fn under_own_name(n: u64) { match n { lower_k => {} _ => { assert!(false); } } }  // refutes
//! #[trust_vc::requires(n < 100)]
//! pub fn under_use_alias(n: u64) { match n { alias_k => {} _ => { assert!(false); } } }  // VERIFIED
//! ```
//!
//! Same const, same file, two names, two verdicts. `const_pattern_desugar`
//! collected declaration idents only, so the alias fell through to the
//! bare-binder answer, made the wildcard arm's prior-negation `!(true)` — FALSE
//! — and vacuously discharged `assert!(false)`. An UPPERCASE const renamed to a
//! lowercase local defeats the registry too, so it is not a case residual.
//!
//! The fix resolves the file's top-level `use` items back to the item they NAME
//! and enters the LOCAL name in the same registry: the declaration decides, not
//! the spelling.
//!
//! The narrowness pin runs the other way and is load-bearing: an import that
//! resolves to a fn, a type or a struct with fields is NOT a const pattern, so
//! `use std::cmp::min;` must leave `match n { min => .. }` binding.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx() -> String {
    format!(
        "{}/tests/data/const_pattern_use_alias_soundness.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(name: &str) -> Result<VerifyResult, trust_vc_core::TrustVcError> {
    let v = verify_function_from_file(&fx(), name);
    eprintln!("[CONSTPAT-USE] {name} => {v:?}");
    v
}

// ---- THE CARDINAL FALSE VERIFY --------------------------------------------

#[test]
fn alias_arm_must_not_vacuously_discharge_its_sibling() {
    let v = verdict("alias_sibling_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: a `use crate::lower_k as alias_k` arm was treated as an \
         irrefutable binder, so the wildcard arm's guard became FALSE and \
         `assert!(false)` was vacuously discharged; got {v:?}"
    );
}

#[test]
fn upper_const_aliased_to_a_lowercase_local_must_not_verify() {
    let v = verdict("upper_const_aliased_to_lower_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: the alias defeats the registry regardless of the const's \
         own spelling, so this is not a case-heuristic residual; got {v:?}"
    );
}

#[test]
fn cross_module_import_must_not_verify() {
    let v = verdict("cross_module_import_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: an imported cross-module const is still a const pattern; \
         got {v:?}"
    );
}

/// THE CONTROL. The declaration route was already closed at `fec7159c`; if it
/// ever regresses, the paired assertions above stop discriminating.
#[test]
fn own_name_route_still_refutes() {
    let v = verdict("own_name_sibling_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "the same const under its DECLARED name must refute — it is what the \
         aliased form is compared against; got {v:?}"
    );
}

/// THE DISCRIMINATOR. The literal twin is the same Rust program.
#[test]
fn literal_twin_still_refutes() {
    let v = verdict("literal_twin_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "the literal control must refute; got {v:?}"
    );
}

// ---- LIAR PINS -------------------------------------------------------------

#[test]
fn alias_arm_liar_must_not_verify() {
    let v = verdict("alias_arm_liar_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "LIAR PIN: the aliased arm supplies `n == 5`, never `n == 6`; got {v:?}"
    );
}

#[test]
fn alias_wildcard_liar_must_not_verify() {
    let v = verdict("alias_wildcard_liar_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "LIAR PIN: the sibling arm is reached only when `n != 5`; got {v:?}"
    );
}

// ---- CAPABILITY ------------------------------------------------------------

#[test]
fn alias_arm_supplies_its_value() {
    let v = verdict("alias_arm_supplies_its_value");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "CAPABILITY: resolving the alias folds it to its literal, so the \
         selected arm must know `n == 5`; got {v:?}"
    );
}

#[test]
fn alias_wildcard_knows_the_negation() {
    let v = verdict("alias_wildcard_knows_the_negation");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "CAPABILITY: the sibling arm must know `n != 5` — the obligation that \
         used to be vacuous; got {v:?}"
    );
}

// ---- NARROWNESS PINS -------------------------------------------------------
// Only CONST aliases may change behaviour. These are the capability disaster
// the fix must not cause.

#[test]
fn ordinary_binder_still_binds_among_imports() {
    let v = verdict("ordinary_binder_still_binds_among_imports");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: a binder naming no import must still bind — the \
         overwhelmingly common case; got {v:?}"
    );
}

#[test]
fn fn_alias_binder_still_binds() {
    let v = verdict("fn_alias_binder_still_binds");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: `use ... as min` names a FUNCTION, which a bare pattern \
         ident cannot resolve to, so `min` still binds; got {v:?}"
    );
}

#[test]
fn fn_alias_binder_liar_must_not_verify() {
    let v = verdict("fn_alias_binder_liar_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "a binder binds the scrutinee, it does not constrain it; got {v:?}"
    );
}

#[test]
fn type_alias_binder_still_binds() {
    let v = verdict("type_alias_binder_still_binds");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: an aliased TYPE import leaves an ordinary binder; got {v:?}"
    );
}

#[test]
fn struct_alias_binder_still_binds() {
    let v = verdict("struct_alias_binder_still_binds");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: an aliased struct-with-fields import leaves an ordinary \
         binder; got {v:?}"
    );
}

// ---- NESTED SCOPES ---------------------------------------------------------

#[test]
fn nested_module_alias_must_not_verify() {
    let v = verdict("nested_alias_sibling_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: a `use` inside an inline `mod` was invisible, so the same \
         cardinal hole survived one level down; got {v:?}"
    );
}

#[test]
fn nested_fn_does_not_inherit_a_file_top_level_const() {
    let v = verdict("nested_top_level_const_is_a_binder_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: a file-top-level `const` is NOT in scope inside `mod`, so \
         the name is a BINDER there; folding it narrowed the arm's path \
         condition and discharged a false claim; got {v:?}"
    );
}

#[test]
fn nested_module_fn_alias_binder_still_binds() {
    let v = verdict("nested_fn_alias_binder_still_binds");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: the fn/type carve-out holds at nesting depth too; got {v:?}"
    );
}

// ---- FAIL CLOSED, NOT GUESSED ----------------------------------------------

#[test]
fn unresolvable_import_must_not_verify() {
    let v = verdict("unresolvable_import_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "an import this file cannot resolve (out-of-line module, external crate) \
         must fail closed, not be guessed as a binder; got {v:?}"
    );
}
