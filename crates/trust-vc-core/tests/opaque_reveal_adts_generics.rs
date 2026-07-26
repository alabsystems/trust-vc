// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! End-to-end (source-catalog path, via `verify_function_from_file`) coverage
//! for opaque spec fns + `reveal!`, mirroring upstream Verus
//! `rust_verify_test/tests/adts_generics.rs` (test_refinements1,
//! test_refinements1_fail, test_refinements2, test_triggers) plus two
//! adversarial soundness probes the upstream file does not contain but which
//! the opaque/reveal contract demands:
//!
//!   * an UNREVEALED opaque fn must stay truly uninterpreted (a goal needing
//!     its body must fail closed, never falsely Verified);
//!   * a recursive opaque fn with no `#[decreases]` keeps its body axiom
//!     suppressed even under `reveal!` (no unsound proof of false).
//!
//! See `tests/data/opaque_reveal_adts_generics.rs` for the source under test
//! and the faithful-adaptation note (generic `id<A>` -> concrete `id(int)`).
//!
//! The encoder-level filter these exercise (skip an opaque body axiom unless
//! revealed; fall through to add_typed_broadcast / encode_fuel_axioms when
//! revealed) lives at encoder/verification/setup_broadcasts.rs and is unit
//! tested in encoder/tests/reveal_hide.rs; this file pins the behaviour through
//! the full file-extraction surface.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/opaque_reveal_adts_generics.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verify(func: &str) -> VerifyResult {
    verify_function_from_file(&path(), func)
        .unwrap_or_else(|e| panic!("{func} should extract+verify, got error: {e}"))
}

// ───────────────────────── positive: reveal load-bearing ─────────────────────────

#[test]
fn test_refinements1_verifies_with_reveal() {
    let v = verify("refinements1");
    assert!(
        matches!(v, VerifyResult::Verified),
        "revealed opaque id: id(y.u) >= 0 must follow from y.u >= 0 and id(y.u) == y.u; got {v:?}"
    );
}

#[test]
fn test_refinements2_struct_field_verifies_with_reveal() {
    let v = verify("refinements2");
    assert!(
        matches!(v, VerifyResult::Verified),
        "revealed opaque id over a struct field: id(p.a) >= 0 must verify; got {v:?}"
    );
}

#[test]
fn test_triggers_struct_field_verifies() {
    let v = verify("triggers_struct_field");
    assert!(
        matches!(v, VerifyResult::Verified),
        "opaque fi as a forall trigger head + reveal: fi(s.i) must discharge; got {v:?}"
    );
}

#[test]
fn test_triggers_struct_constructor_verifies() {
    let v = verify("triggers_struct_constructor");
    assert!(
        matches!(v, VerifyResult::Verified),
        "opaque fs(S{{..}}) as a forall trigger + reveal: fs(S{{i:5}}) must discharge; got {v:?}"
    );
}

// ───────────────────────── negative: revealed but unprovable ─────────────────────────

#[test]
fn test_refinements1_fail_counterexample() {
    let v = verify("refinements1_fail");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "id(y.u) >= 1 does NOT follow from y.u >= 0 (witness 0) even revealed; \
         must be a counterexample, got {v:?}"
    );
}

// ───────────────────────── adversarial: fail-closed soundness ─────────────────────────

#[test]
fn test_unrevealed_opaque_is_truly_uninterpreted() {
    // The crux of the soundness contract: with NO reveal, the body fact
    // id(y.u) == y.u must be unprovable — id is a pure uninterpreted function.
    let v = verify("refinements1_unrevealed");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "UNSOUND: an UNREVEALED opaque fn leaked its body (id(a) == a verified \
         without reveal). Verdict: {v:?}"
    );
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "unrevealed opaque body fact should fail closed with a counterexample, got {v:?}"
    );
}

#[test]
fn test_recursive_opaque_without_decreases_does_not_prove_false() {
    // reveal! must not resurrect the suppressed unsound-recursion axiom.
    let v = verify("recursive_opaque_no_decreases_proves_false");
    assert!(
        !matches!(v, VerifyResult::Verified),
        "UNSOUND: a recursive opaque fn with no #[decreases] proved a false \
         statement via its (must-be-suppressed) defining axiom. Verdict: {v:?}"
    );
}
