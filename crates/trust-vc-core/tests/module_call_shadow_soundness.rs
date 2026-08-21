// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! FV-A: a call resolved against the wrong function because the call-path key
//! omitted the CALLER's inline-module scope.
//!
//! `SourceFunctionRegistry` is keyed by the DECLARATION's inline-module path
//! (`app::util::f`) but was looked up with the path exactly as WRITTEN at the
//! call site (`util::f`), i.e. read as file-root-relative. A call inside
//! `mod app` therefore resolved to a same-named item at FILE scope, and the
//! verifier reasoned about a different function's body, `requires` AND
//! `ensures` than the one Rust calls. The bare-spelling half of the same hole
//! lives in the spec catalog, whose key is the ident alone.
//!
//! This is the call-path twin of FV-1 (`module_type_shadow_soundness.rs`): a
//! registry keyed on an identifier that is not unique in the file.
//!
//! Each group below carries BOTH halves of a real fix:
//!   * the false program must stop reporting `Verified`, and
//!   * a TRUE program of the same shape must still verify, so the fix cannot
//!     degenerate into "decline every colliding call path".
//! Every shadow case also has an ORDER-FLIP control: the verdict must be
//! identical with the declarations swapped, which is what catches a resolver
//! that is wrong in either direction.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx(name: &str) -> String {
    format!("{}/tests/data/{name}", env!("CARGO_MANIFEST_DIR"))
}

const SCOPE: &str = "module_call_shadow_scope.rs";
const SCOPE_FLIP: &str = "module_call_shadow_scope_flip.rs";
const TRUE_SHAPE: &str = "module_call_shadow_true.rs";
const TRUE_SHAPE_FLIP: &str = "module_call_shadow_true_flip.rs";
const PINS: &str = "module_call_shadow_pins.rs";
const BARE_SPEC: &str = "module_call_shadow_bare_spec.rs";
const BARE_SPEC_FLIP: &str = "module_call_shadow_bare_spec_flip.rs";
const SPEC_UNSHADOWED: &str = "module_call_shadow_spec_unshadowed.rs";
const SPEC_QUALIFIED: &str = "module_call_shadow_spec_qualified.rs";

fn assert_not_verified(fixture: &str, function: &str, why: &str) {
    let verdict = verify_function_from_file(&fx(fixture), function);
    assert!(
        !matches!(verdict, Ok(VerifyResult::Verified)),
        "{fixture}::{function} must NOT verify — {why}; got {verdict:?}"
    );
}

fn assert_verified(fixture: &str, function: &str, why: &str) {
    let verdict = verify_function_from_file(&fx(fixture), function);
    assert!(
        matches!(verdict, Ok(VerifyResult::Verified)),
        "{fixture}::{function} must still verify — {why}; got {verdict:?}"
    );
}

// ---- FALSE-VERIFY: qualified call path -------------------------------------

/// `mod app`'s `util::f(x)` is `app::util::f`, which subtracts 10. The stated
/// `ensures(result == x)` is false for it (rustc: `app::call(50) == 40`), and
/// the callee's `requires(x >= 10)` was dropped as well, hiding a `u32`
/// underflow at `call(1)`.
#[test]
fn inline_module_call_does_not_resolve_to_the_file_scope_function() {
    assert_not_verified(
        SCOPE,
        "call",
        "`util::f` inside `mod app` names `app::util::f` (x - 10), not the \
         top-level identity `util::f`",
    );
}

/// ORDER-FLIP CONTROL. Same two declarations, `mod app` written first.
#[test]
fn inline_module_call_verdict_is_declaration_order_independent() {
    assert_not_verified(
        SCOPE_FLIP,
        "call",
        "scope decides the callee, so swapping the declarations must not change \
         the verdict",
    );
}

/// NARROWNESS PIN. The same shadowing file with a contract that states what
/// `app::util::f` really does. `Verified` here is what separates "resolved to
/// the inner declaration" from "declined because the name collides" — under the
/// top-level identity `f`, `result == x - 10` is refutable.
#[test]
fn inline_module_call_resolves_to_the_inner_declaration() {
    assert_verified(
        TRUE_SHAPE,
        "call",
        "a TRUE contract over the actually-called `app::util::f` must still be \
         provable; a blanket decline would fail here",
    );
}

/// ORDER-FLIP CONTROL for the narrowness pin.
#[test]
fn inline_module_call_resolution_survives_declaration_flip() {
    assert_verified(
        TRUE_SHAPE_FLIP,
        "call",
        "the narrowness pin must hold in both declaration orders",
    );
}

// ---- FALSE-VERIFY: bare call spelling --------------------------------------

/// The minimal form: no sub-module, no qualifier. `mod inner`'s own `v` shadows
/// the top-level spec fn of the same name (rustc: `inner::bare_shadow()` is
/// `false`, against `ensures(result)`).
#[test]
fn bare_call_inside_a_module_does_not_resolve_to_the_file_scope_spec() {
    assert_not_verified(
        BARE_SPEC,
        "bare_shadow",
        "`v()` inside `mod inner` names `inner::v` (false), not the top-level \
         `v` (true)",
    );
}

/// ORDER-FLIP CONTROL for the bare spelling.
#[test]
fn bare_call_verdict_is_declaration_order_independent() {
    assert_not_verified(
        BARE_SPEC_FLIP,
        "bare_shadow",
        "the shadow depends on the SET of declarations, not on which is written \
         first",
    );
}

/// NARROWNESS PIN. With no nested re-declaration, a bare `v()` written inside a
/// module still resolves to the top-level spec fn.
#[test]
fn unshadowed_bare_spec_call_still_resolves() {
    assert_verified(
        SPEC_UNSHADOWED,
        "uses_top",
        "an ident with exactly one declaration in the file is not a collision",
    );
}

/// NARROWNESS PIN. The shadow exists, but the use site writes the
/// module-qualified spelling, which is unambiguous. Proving `!result` also
/// discriminates: the top-level `v` is `true`.
#[test]
fn qualified_spelling_of_a_shadowed_spec_still_resolves() {
    assert_verified(
        SPEC_QUALIFIED,
        "qualified_shadowed",
        "`inner::v()` names one declaration outright, so the bare-key strike \
         must not reach it",
    );
}

// ---- NARROWNESS PINS: ordinary, non-colliding call shapes ------------------

/// A non-colliding cross-module call: `mod a` calling `b::g` where `g` is
/// unique. This is the shape the scope walk must NOT break.
#[test]
fn non_colliding_cross_module_call_still_verifies() {
    assert_verified(
        PINS,
        "cross_module_bare",
        "`b::g` is unique in the file; the outward scope walk must find it from \
         `mod a`",
    );
}

#[test]
fn crate_rooted_cross_module_call_still_verifies() {
    assert_verified(
        PINS,
        "cross_module_crate",
        "a `crate::`-rooted spelling keeps its file-root reading",
    );
}

#[test]
fn same_module_sibling_call_still_verifies() {
    assert_verified(PINS, "same_module", "the innermost scope holds the callee");
}

#[test]
fn super_qualified_call_resolves_to_the_parent_module() {
    assert_verified(
        PINS,
        "via_super",
        "`super::bump` names exactly one level up from `outer::nested`",
    );
}

#[test]
fn self_qualified_call_resolves_to_the_own_module() {
    assert_verified(PINS, "via_self", "`self::step` names `selfmod::step`");
}
