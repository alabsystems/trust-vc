// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Deciding a bare pattern ident by DECLARATION only helps if the declaration
//! is SEEN. `const_pattern_desugar`'s first collector walked `Item::Mod`
//! content and the top-level statement items of an `Item::Fn` block, and
//! nothing else — so a `const` (or a `use` alias) declared in an `impl` method
//! body, a trait DEFAULT method body, or ANY nested block was never registered.
//! The name stayed a bare lowercase ident, `arm_pattern_match_condition`
//! answered `Always`, the sibling arm's prior-negation became `!(true)` —
//! FALSE — and every obligation in it was vacuously discharged:
//!
//! ```ignore
//! impl S {
//!     #[trust_vc::requires(n < 100)]
//!     pub fn f(n: u64) {
//!         const lower_k: u64 = 5;
//!         match n { lower_k => {} _ => { assert!(false); } }   // VERIFIED
//!     }
//! }
//! ```
//!
//! The SPELLING axis was already closed (11 spellings) and did not reach this:
//! the same const name, the same file, moved one scope inward, flipped the
//! verdict. Twelve container shapes verified.
//!
//! The fix walks the whole file with `syn::visit::Visit` rather than adding a
//! match arm per container, so the shapes below are a SAMPLE of a closed set
//! rather than the enumeration the fix keys on. Each is paired here with the
//! narrowness pin that must survive it — an ordinary lowercase binder still
//! binds in every one of those scopes, which is the overwhelmingly common case
//! and the thing a blanket rejection would destroy.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx() -> String {
    format!(
        "{}/tests/data/const_pattern_scope_soundness.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(name: &str) -> Result<VerifyResult, trust_vc_core::TrustVcError> {
    let v = verify_function_from_file(&fx(), name);
    eprintln!("[CONSTPAT-SCOPE] {name} => {v:?}");
    v
}

fn must_not_verify(name: &str, scope: &str) {
    let v = verdict(name);
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: a const/alias declared in {scope} was invisible to the \
         declaration registry, so its arm was classified `Always` and the \
         sibling arm's prior-negation `!(true)` vacuously discharged \
         `assert!(false)`; got {v:?}"
    );
}

fn must_verify(name: &str, why: &str) {
    let v = verdict(name);
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS/CAPABILITY PIN: {why}; got {v:?}"
    );
}

// ---- THE CARDINAL FALSE VERIFIES, ONE PER CONTAINER SHAPE ------------------

#[test]
fn const_in_an_impl_method_body_must_not_vacuously_discharge_its_sibling() {
    must_not_verify(
        "impl_body_const_sibling_must_not_verify",
        "an `impl` method body",
    );
}

#[test]
fn const_in_a_trait_default_body_must_not_vacuously_discharge_its_sibling() {
    must_not_verify(
        "trait_default_const_sibling_must_not_verify",
        "a trait DEFAULT method body",
    );
}

#[test]
fn const_in_a_nested_block_must_not_vacuously_discharge_its_sibling() {
    must_not_verify(
        "nested_block_const_sibling_must_not_verify",
        "a nested block",
    );
}

/// The shape that proves the fix is not three extra match arms: adding
/// `Item::Impl`/`Item::Trait` descent alone leaves this one verifying.
#[test]
fn const_in_a_nested_block_inside_an_impl_method_must_not_vacuously_discharge() {
    must_not_verify(
        "impl_nested_block_const_sibling_must_not_verify",
        "a nested block inside an `impl` method body",
    );
}

#[test]
fn const_in_an_if_block_must_not_vacuously_discharge_its_sibling() {
    must_not_verify("if_block_const_sibling_must_not_verify", "an `if` block");
}

#[test]
fn const_in_a_loop_body_must_not_vacuously_discharge_its_sibling() {
    must_not_verify("loop_body_const_sibling_must_not_verify", "a loop body");
}

#[test]
fn const_in_a_match_arm_block_must_not_vacuously_discharge_its_sibling() {
    must_not_verify(
        "match_arm_const_sibling_must_not_verify",
        "a match-arm block",
    );
}

#[test]
fn const_in_an_impl_inside_a_module_must_not_vacuously_discharge_its_sibling() {
    must_not_verify(
        "mod_impl_const_sibling_must_not_verify",
        "an `impl` method body inside an inline `mod`",
    );
}

/// A `static` shares the value namespace with a `const`, so it shares the hole.
#[test]
fn static_in_an_impl_method_body_must_not_vacuously_discharge_its_sibling() {
    must_not_verify(
        "impl_body_static_sibling_must_not_verify",
        "an `impl` method body (a `static`)",
    );
}

// ---- THE SAME HOLE ONE ALIAS DEEP ------------------------------------------
// A `use` introduces a second NAME for the same const. Being in an unwalked
// scope defeated the declaration registry for the alias exactly as it did for
// the declaration.

#[test]
fn use_alias_in_an_impl_method_body_must_not_vacuously_discharge_its_sibling() {
    must_not_verify(
        "impl_body_use_alias_sibling_must_not_verify",
        "an `impl` method body (a `use` alias)",
    );
}

#[test]
fn use_alias_in_a_nested_block_must_not_vacuously_discharge_its_sibling() {
    must_not_verify(
        "nested_block_use_alias_sibling_must_not_verify",
        "a nested block (a `use` alias)",
    );
}

#[test]
fn use_alias_in_a_trait_default_body_must_not_vacuously_discharge_its_sibling() {
    must_not_verify(
        "trait_default_use_alias_sibling_must_not_verify",
        "a trait DEFAULT method body (a `use` alias)",
    );
}

// ---- NARROWNESS PINS -------------------------------------------------------
// Load-bearing. Failing closed on every bare ident in these scopes would pass
// every probe above and be a capability disaster: an ordinary lowercase binder
// is the overwhelmingly common case.

#[test]
fn ordinary_binder_in_an_impl_method_body_still_binds() {
    must_verify(
        "impl_body_binder_still_binds",
        "an ordinary lowercase binder in an `impl` method body must still BIND",
    );
}

/// The DISCRIMINATOR for the pin above. A binder binds the scrutinee, it does
/// not constrain it — if this ever verifies, the pin is proving nothing.
#[test]
fn impl_body_binder_liar_must_not_verify() {
    let v = verdict("impl_body_binder_liar_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "a binder supplies no value fact, so `result == n + 1` must refute; \
         got {v:?}"
    );
}

#[test]
fn ordinary_binder_in_a_nested_block_inside_an_impl_method_still_binds() {
    must_verify(
        "impl_nested_block_binder_still_binds",
        "a binder in a nested block inside an `impl` method must still BIND",
    );
}

#[test]
fn ordinary_binder_in_a_trait_default_body_still_binds() {
    must_verify(
        "trait_default_binder_still_binds",
        "a binder in a trait DEFAULT method body must still BIND",
    );
}

#[test]
fn ordinary_binder_in_a_nested_block_still_binds() {
    must_verify(
        "nested_block_binder_still_binds",
        "a binder in a nested block must still BIND",
    );
}

/// Walking `impl` bodies must not start collecting ASSOCIATED consts: a bare
/// `bound_assoc` never resolves to `Assoc::bound_assoc`, so collecting one
/// would convert a genuine binder into a fail-closed marker.
#[test]
fn binder_colliding_with_an_impl_associated_const_still_binds() {
    must_verify(
        "binder_colliding_with_impl_assoc_const_still_binds",
        "an `impl` ASSOCIATED const is not a bare-name pattern and must not be \
         collected",
    );
}

#[test]
fn binder_colliding_with_a_trait_associated_const_still_binds() {
    must_verify(
        "binder_colliding_with_trait_assoc_const_still_binds",
        "a trait ASSOCIATED const is not a bare-name pattern and must not be \
         collected",
    );
}

/// Only CONST-like imports may change behaviour. An alias of a FUNCTION in a
/// newly walked scope must still leave a same-named binder alone elsewhere.
#[test]
fn fn_alias_in_an_impl_method_body_leaves_a_binder_alone() {
    must_verify(
        "fn_alias_leaves_a_binder_alone",
        "a `use` resolving to a fn leaves an ordinary BINDER — `use \
         std::cmp::min;` plus `match n { min => .. }` depends on it",
    );
}

// ---- CAPABILITY PINS -------------------------------------------------------
// Proving less is not a fix. The alias fold is also the pin on the collector's
// top-level `use` bookkeeping: gathering a file-scope alias twice would demote
// it to the fail-closed marker and silently retire this capability.

#[test]
fn file_scope_alias_arm_still_folds_and_supplies_its_value() {
    must_verify(
        "top_level_alias_arm_still_folds",
        "a FILE-SCOPE const alias must still fold and supply `n == 5`",
    );
}

#[test]
fn file_scope_alias_arm_liar_must_not_verify() {
    let v = verdict("top_level_alias_arm_liar_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "the alias arm supplies `n == 5`, so `n == 6` must refute — otherwise \
         the capability pin above is vacuous; got {v:?}"
    );
}

#[test]
fn file_scope_const_arm_still_folds_and_supplies_its_value() {
    must_verify(
        "top_level_const_arm_still_folds",
        "a FILE-SCOPE const must still fold and supply `n == 7`",
    );
}

#[test]
fn file_scope_const_arm_liar_must_not_verify() {
    let v = verdict("top_level_const_arm_liar_must_not_verify");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "the const arm supplies `n == 7`, so `n == 8` must refute; got {v:?}"
    );
}
