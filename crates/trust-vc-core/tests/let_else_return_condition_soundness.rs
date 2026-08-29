// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Cardinal false-verify regression: the `let PAT = … else { return … };` tail
//! return model derived its match condition from a predicate hand-copied into
//! `vc_extraction.rs`, which had drifted away from
//! `body_extract::pattern_match_condition_for_scoped_value` — the copy returned
//! a bare `String` whose unrecognized arms all yielded `"true"`, applied the
//! `Some`/`None` spelling without checking the scrutinee was an `Option`, and
//! carried neither the `Pat::Struct` refutability gate nor the refinement-drop
//! guards. A `"true"` condition makes the ELSE value unreachable, so the
//! postcondition is discharged against the tail value alone.
//!
//! Every TARGET here verified before the de-duplication (confirmed through the
//! production CLI, cache off). Every CONTROL verified before AND after: they are
//! the narrowness pins, without which "decline every let-else" would pass.
//!
//! See `tests/data/let_else_return_condition_soundness.rs` for the programs.

use trust_vc_core::{verify_function_from_file, VerifyResult};

const FIXTURE: &str = "let_else_return_condition_soundness.rs";

fn fixture_path() -> String {
    format!("{}/tests/data/{FIXTURE}", env!("CARGO_MANIFEST_DIR"))
}

/// The target's postcondition is FALSE on the else path, so any verdict other
/// than `Verified` is correct — a counterexample when the condition models
/// faithfully, a declined-model error when the pattern is not modelable.
fn must_not_verify(function: &str) {
    let verdict = verify_function_from_file(&fixture_path(), function);
    eprintln!("[TARGET] {function} => {verdict:?}");
    assert!(
        !matches!(verdict, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: {function} — the let-else match condition widened to \
         always-match, so the else value became unreachable"
    );
}

fn must_verify(function: &str) {
    let verdict = verify_function_from_file(&fixture_path(), function);
    eprintln!("[CONTROL] {function} => {verdict:?}");
    assert!(
        matches!(verdict, Ok(VerifyResult::Verified)),
        "OVER-REJECTION: {function} => {verdict:?}"
    );
}

// ---------------------------------------------------------------- TARGETS ---

#[test]
fn struct_pattern_does_not_widen() {
    must_not_verify("struct_pattern_must_not_widen");
    must_not_verify("struct_rest_pattern_must_not_widen");
}

#[test]
fn field_and_element_refinements_are_not_dropped() {
    must_not_verify("struct_field_literal_must_not_drop");
    must_not_verify("tuple_struct_element_literal_must_not_drop");
    must_not_verify("tuple_struct_at_subpattern_must_not_drop");
}

#[test]
fn scalar_value_patterns_do_not_widen() {
    must_not_verify("literal_pattern_must_not_widen");
    must_not_verify("range_pattern_must_not_widen");
    must_not_verify("tuple_pattern_literal_must_not_widen");
}

#[test]
fn compound_patterns_do_not_widen() {
    must_not_verify("or_pattern_must_not_widen");
    must_not_verify("reference_pattern_must_not_widen");
    must_not_verify("slice_pattern_must_not_widen");
}

#[test]
fn const_patterns_are_not_read_as_bindings() {
    must_not_verify("bare_const_ident_pattern_must_not_widen");
    must_not_verify("path_const_pattern_must_not_widen");
}

#[test]
fn top_level_at_binding_does_not_widen() {
    must_not_verify("top_level_at_binding_must_not_widen");
}

// --------------------------------------------------------------- CONTROLS ---
// NARROWNESS PINS — a blanket decline passes every target above and fails here.

#[test]
fn irrefutable_let_else_still_models() {
    must_verify("irrefutable_binder_still_verifies");
    must_verify("irrefutable_binder_unresolvable_scrutinee_still_verifies");
    must_verify("irrefutable_struct_pattern_still_verifies");
}

#[test]
fn refutable_let_else_the_handler_models_still_verifies() {
    must_verify("refutable_tuple_struct_still_verifies");
    must_verify("refutable_option_still_verifies");
    must_verify("let_local_scrutinee_still_verifies");
}

/// The discriminating pin: provable ONLY when the condition is the real variant
/// test. Forcing the condition back to `"true"` (the pre-fix behaviour) turns
/// this into a counterexample, so it fails in the opposite direction from the
/// targets and cannot be satisfied by the same mistake.
#[test]
fn else_value_is_still_reachable() {
    must_verify("else_value_stays_reachable");
}
