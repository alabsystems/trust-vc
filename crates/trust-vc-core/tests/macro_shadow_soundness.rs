// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Macro NAMES were resolved by spelling, never by resolution.
//!
//! Every lane that gives a macro a meaning identified it by its bare ident, or
//! by the LAST segment of its path with every qualifier discarded. A
//! `macro_rules! assume` in the file, a `use util::noop as assume`, an
//! `m::assume!` — all three were read as trust-vc's `assume!` and consumed as a
//! spec ASSUMPTION, which buys a proof of anything. A shadowed `matches!` got
//! BOTH directions wrong at once: the false claim verified and the true claim
//! was refuted.
//!
//! Six reproducers below, all legal single-file Rust, all confirmed against
//! `rustc --edition 2021` (the user macro wins at every one of these call
//! sites), all green under the production CLI before the fix.
//!
//! What this file pins is that no spelling of a shadowed or foreign-qualified
//! special macro can produce `Verified`. The narrowness half — that the
//! unambiguous spellings still resolve and still verify AND still refute — is
//! at the bottom, and it is what separates this fix from a blanket rejection.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx(n: &str) -> String {
    format!("{}/tests/data/{n}", env!("CARGO_MANIFEST_DIR"))
}

const SHADOW: &str = "macro_shadow_soundness.rs";
const QUALIFIED: &str = "macro_shadow_qualified.rs";
const USE_ALIAS: &str = "macro_shadow_use_alias.rs";
const TRUST_VC_RENAME: &str = "macro_shadow_trust_vc_rename.rs";
const DECL_MACRO: &str = "macro_shadow_decl_macro.rs";
const REBOUND_ROOT: &str = "macro_shadow_rebound_root.rs";
const NARROWNESS: &str = "macro_shadow_narrowness.rs";

fn must_not_verify(file: &str, func: &str, why: &str) {
    let v = verify_function_from_file(&fx(file), func);
    eprintln!("[MACRO-SHADOW] {file}::{func} => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: {why}; got {v:?}"
    );
}

fn must_verify(file: &str, func: &str, why: &str) {
    let v = verify_function_from_file(&fx(file), func);
    eprintln!("[MACRO-SHADOW-PIN] {file}::{func} => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "NARROWNESS PIN: {why}; got {v:?}"
    );
}

// ---------------- CARDINAL: a shadowed name must not buy a proof -----------

#[test]
fn a_shadowed_assume_must_not_verify() {
    must_not_verify(
        SHADOW,
        "shadowed_assume_must_not_verify",
        "a user `macro_rules! assume` is a NO-OP, and consuming it as a spec \
         assumption proves `x <= 255` for an unconstrained u64",
    );
}

#[test]
fn a_shadowed_matches_must_not_verify() {
    must_not_verify(
        SHADOW,
        "shadowed_matches_must_not_verify",
        "the user `matches!` yields `false`, so `assert!(matches!(y, 7u8))` is \
         false — desugaring it to std's expansion made it verify",
    );
}

/// The other direction of the SAME defect, and the reason it is cardinal rather
/// than merely wrong: the claim that is TRUE under the user's macro was
/// refuted. A fix that only stops the false verify would leave this refuting.
#[test]
fn a_shadowed_matches_must_not_be_refuted_as_if_it_were_stds() {
    let v = verify_function_from_file(&fx(SHADOW), "shadowed_matches_negation_is_true");
    eprintln!("[MACRO-SHADOW] {SHADOW}::shadowed_matches_negation_is_true => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Counterexample { .. })),
        "the claim is TRUE under the user's macro; producing a counterexample for \
         it means the desugar is still reading std's `matches!`; got {v:?}"
    );
}

/// No `syn` visitor descends into a macro's token stream, so this position is
/// unreachable for any gate that enumerates AST macro positions.
#[test]
fn a_shadowed_assume_nested_in_a_proof_block_must_not_verify() {
    must_not_verify(
        SHADOW,
        "shadowed_assume_in_proof_block_must_not_verify",
        "the shadowed `assume!` inside `proof_block!`'s TOKEN STREAM was still \
         consumed as a spec assumption",
    );
}

#[test]
fn a_shadowed_assume_nested_in_assert_by_must_not_verify() {
    must_not_verify(
        SHADOW,
        "shadowed_assume_in_assert_by_must_not_verify",
        "same token-stream route, through `assert_by!`'s proof block",
    );
}

#[test]
fn a_shadowed_matches_in_a_contract_attribute_must_not_verify() {
    must_not_verify(
        SHADOW,
        "shadowed_matches_in_contract_must_not_verify",
        "a contract attribute carries its predicate as an opaque token stream — \
         a third position no AST walk reaches",
    );
}

// ---------------- CARDINAL: every other way to bind the name ---------------

#[test]
fn a_qualified_user_macro_must_not_verify() {
    must_not_verify(
        QUALIFIED,
        "qualified_user_assume_must_not_verify",
        "`m::assume!` names a macro in `m`; discarding the qualifier made it \
         trust-vc's `assume!`",
    );
}

#[test]
fn a_module_local_shadow_must_not_verify_inside_that_module() {
    must_not_verify(
        QUALIFIED,
        "module_local_assume_must_not_verify",
        "inside `mod m`, the bare `assume!` IS `m`'s no-op macro",
    );
}

#[test]
fn a_use_alias_onto_a_special_name_must_not_verify() {
    must_not_verify(
        USE_ALIAS,
        "use_aliased_assume_must_not_verify",
        "`use util::noop as assume;` binds the name with no `macro_rules! assume` \
         anywhere in the file",
    );
}

/// The case that kills "check whether the import comes from trust-vc": it does,
/// and it still means a different macro.
#[test]
fn a_rename_of_a_different_trust_vc_macro_must_not_verify() {
    must_not_verify(
        TRUST_VC_RENAME,
        "trust_vc_rename_must_not_verify",
        "`use trust_vc::hide as assume;` points INTO trust-vc but binds `assume` \
         to `hide!`, which assumes nothing",
    );
}

/// `syn` 2 has no node for a declarative macro 2.0 — it arrives as
/// `Item::Verbatim`, which an item-kind match silently walks past.
#[test]
fn a_decl_macro_2_shadow_must_not_verify() {
    must_not_verify(
        DECL_MACRO,
        "decl_macro_assume_must_not_verify",
        "`pub macro assume($e:expr) {}` binds the name exactly as `macro_rules!` \
         does",
    );
}

/// An allowlist of qualifier ROOTS is worth nothing if the file can rebind the
/// root out from under it.
#[test]
fn a_rebound_qualifier_root_must_not_verify() {
    must_not_verify(
        REBOUND_ROOT,
        "rebound_root_must_not_verify",
        "`mod trust_vc { .. }` makes `trust_vc::assume!` name the LOCAL module's \
         no-op macro",
    );
}

// ---------------- NARROWNESS PINS: the fix must not blanket-reject ---------

#[test]
fn the_bare_spelling_still_verifies() {
    must_verify(
        NARROWNESS,
        "bare_assume_still_verifies",
        "unqualified `assume!` with nothing shadowing it is trust-vc's — 78 \
         occurrences in the ported corpus depend on it",
    );
}

#[test]
fn the_qualified_spelling_still_verifies() {
    must_verify(
        NARROWNESS,
        "qualified_assume_still_verifies",
        "`trust_vc::assume!` — 197 occurrences in the ported corpus",
    );
}

#[test]
fn matches_still_desugars() {
    must_verify(
        NARROWNESS,
        "matches_still_verifies",
        "an unshadowed `matches!` must still be rewritten to its `match` \
         expansion",
    );
}

/// The pin that a fail-closed pass cannot fake: a FALSE `matches!` claim has to
/// come back as a counterexample, not as an error.
#[test]
fn a_false_matches_still_refutes() {
    let v = verify_function_from_file(&fx(NARROWNESS), "false_matches_still_refutes");
    eprintln!("[MACRO-SHADOW-PIN] {NARROWNESS}::false_matches_still_refutes => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Counterexample { .. })),
        "NARROWNESS PIN: an unshadowed `matches!` that is false must still yield a \
         COUNTEREXAMPLE — an error here means the pass stopped resolving it at \
         all; got {v:?}"
    );
}

#[test]
fn matches_in_a_contract_attribute_still_verifies() {
    must_verify(
        NARROWNESS,
        "matches_in_contract_still_verifies",
        "the contract-attribute position must keep resolving when nothing \
         shadows the name",
    );
}

#[test]
fn a_function_in_a_nested_module_still_verifies() {
    must_verify(
        NARROWNESS,
        "module_function_still_verifies",
        "module nesting alone must not make a name unresolvable",
    );
}

/// The pin that separates PER-MODULE resolution from a file-wide
/// over-approximation: the very file that contains the `mod m` shadow must
/// still verify the top-level use of the same name.
#[test]
fn a_module_scoped_shadow_does_not_reach_the_parent() {
    must_verify(
        QUALIFIED,
        "top_level_assume_is_unaffected",
        "a `macro_rules!` inside `mod m` is not in scope in the parent module; \
         declining the top-level `assume!` would be a capability loss bought \
         with nothing",
    );
}

// ---- The EXPRESSION-macro lane: the same defect, a different dispatch ------

/// Found by extending the canonical name list to the lane next door — the
/// literal instance of "when a gate enumerates the ways an effect can be
/// SPELLED, the next spelling is a hole".
#[test]
fn a_shadowed_seq_must_not_verify() {
    must_not_verify(
        SHADOW,
        "shadowed_seq_must_not_verify",
        "the user `seq!` yields an EMPTY sequence, so `s.len() == 3` is false",
    );
}

#[test]
fn a_shadowed_equal_must_not_verify() {
    must_not_verify(
        SHADOW,
        "shadowed_equal_must_not_verify",
        "the user `equal!` always yields `false`, so `equal!(x, x)` is false",
    );
}

#[test]
fn the_qualified_ghost_collection_spelling_still_verifies() {
    must_verify(
        NARROWNESS,
        "qualified_seq_still_verifies",
        "`trust_vc_types::seq!` — 284 occurrences in the ported corpus; \
         declining this root would break the whole ghost-collection lane",
    );
}

#[test]
fn the_bare_ghost_collection_spelling_still_verifies() {
    must_verify(
        NARROWNESS,
        "bare_seq_still_verifies",
        "the unqualified `seq!` with nothing shadowing it",
    );
}

/// `crate::` must be resolved against THIS FILE, not waved through as a crate
/// root — otherwise a file's own `macro_rules! assume` would be reachable and
/// believed as `crate::assume!`.
#[test]
fn a_crate_relative_spelling_still_verifies() {
    must_verify(
        NARROWNESS,
        "crate_qualified_seq_still_verifies",
        "`crate::seq!` points back into a file that shadows nothing",
    );
}
