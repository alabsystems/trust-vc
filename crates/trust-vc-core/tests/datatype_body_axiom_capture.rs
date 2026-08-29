// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CARDINAL fail-closed pin for BINDER CAPTURE in the spec-fn defining axiom.
//!
//! See `tests/data/datatype_body_axiom_capture.rs` for the full mechanism. In
//! one line: the axiom body is encoded before its `forall` is built, so a
//! top-level `try_assert_term` issued from inside that encode is captured by the
//! binder, and `bind_datatype_match_result` turned
//! `∀c. next(c) = match c { .. }` into `∀c. next(c) = <top-level const>` —
//! "next is a constant function".
//!
//! Every goal is checked UNDER A HYPOTHESIS so the closed-ground concrete
//! evaluator override is withheld and the verdict genuinely reflects the emitted
//! axiom rather than trust-vc's own evaluator.
//!
//! SCOPE. This file pins the DATATYPE-MATCH INSTANCE. It does NOT establish
//! that the encode-then-close capture class is closed — 47 helpers on
//! `AstExpressionParser` share the shape, and `purified_euclidean_div_mod_literal`
//! was a second live CARDINAL false verify (`half(2) == 5`). The class-level
//! pins, the second closed site and the one known-open site live in
//! `tests/hoist_capture_class.rs`; the class-level fix is
//! `encoder::binder_capture`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/datatype_body_axiom_capture.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn ok(func: &str) -> VerifyResult {
    verify_function_from_file(&path(), func)
        .unwrap_or_else(|e| panic!("extract/verify {func} failed: {e:?}"))
}

/// CARDINAL: a captured body axiom makes the spec fn a CONSTANT function, which
/// proves false equalities between two different applications of it.
#[test]
fn captured_body_axiom_does_not_make_a_spec_fn_constant() {
    for func in ["f_next_constant_collapse", "f_next_red_neq_green"] {
        let result = ok(func);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "FALSE goal {func} must NOT verify — a `Verified` here means the spec-fn \
             body axiom degenerated to `forall c. next(c) == <top-level constant>` \
             (binder capture in bind_datatype_match_result), got {result:?}"
        );
    }
}

/// The other direction of the same discriminator, and the no-over-rejection
/// guard: the correct body axiom still decides a TRUE application.
#[test]
fn correct_body_axiom_still_decides_a_true_application() {
    assert!(
        matches!(ok("t_next_red_is_green"), VerifyResult::Verified),
        "TRUE goal t_next_red_is_green must still Verify, got {:?}",
        ok("t_next_red_is_green")
    );
}
