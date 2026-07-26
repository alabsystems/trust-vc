// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression coverage for the extensionality bridge: a discharged extensional
//! equality (`=~=` / `ext_eq!`) makes the raw/strict equality (`===` /
//! `strict_eq!`) of the same operands available to later obligations
//! (Verus's auto-`ext_equal`), WITHOUT ever fabricating an equality.
//!
//! Cases are verified through `verify_function_from_file` against the fixture
//! `tests/data/extensionality_bridge.rs`, mirroring the upstream `maps.rs` /
//! `sets.rs` strict-eq ports (the `===`/`strict_eq!` surface is not currently
//! routed through the proc-macro `assert!` expansion).

use std::path::{Path, PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/extensionality_bridge.rs")
}

fn verify(case: &str) -> VerifyResult {
    let path = fixture_path();
    let path = path.to_str().expect("fixture path should be UTF-8");
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} should extract from the fixture: {err}"))
}

// ── POSITIVE ────────────────────────────────────────────────────────────────

/// Upstream sets.rs test1 shape: `assert(a =~= b); assert(a === b)`. The proven
/// extensional equality is carried forward and the bridge discharges the strict
/// equality. This was Unknown before the bridge/carry-forward landed.
#[test]
fn proven_extensional_eq_unlocks_strict_eq() {
    let result = verify("proven_exteq_then_strict");
    assert!(
        matches!(result, VerifyResult::Verified),
        "a proven `=~=` must make the following `===` verify, got {result:?}"
    );
}

/// Strict `===` discharged directly from a genuine extensional-equality
/// hypothesis (membership equality), no intermediate `=~=`.
#[test]
fn strict_eq_from_membership_hypothesis() {
    let result = verify("strict_from_membership_hypothesis");
    assert!(
        matches!(result, VerifyResult::Verified),
        "`===` must verify from an established extensional-equality hypothesis, got {result:?}"
    );
}

/// Task's literal `=~=` then `==` shape over two concrete sets built two ways.
/// (Plain collection `==` is already extensional, so this verified pre-bridge.)
#[test]
fn concrete_extensional_eq_then_plain_eq() {
    let result = verify("concrete_exteq_then_eq");
    assert!(
        matches!(result, VerifyResult::Verified),
        "concrete `=~=` then `==` must verify, got {result:?}"
    );
}

// ── SOUNDNESS ─────────────────────────────────────────────────────────────

/// Adversarial #1: with NO preceding (discharged) `=~=`, strict `===` over
/// provably-distinct sets must fail closed. The bridge must not fabricate `==`.
#[test]
fn strict_eq_over_distinct_sets_without_exteq_fails_closed() {
    let result = verify("strict_distinct_no_exteq");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "`===` over provably-distinct sets without an established `=~=` must NOT verify, \
         got {result:?}"
    );
}

/// Adversarial #1b: strict `===` over unconstrained symbolic sets, no
/// hypothesis at all — must fail closed.
#[test]
fn strict_eq_without_any_hypothesis_fails_closed() {
    let result = verify("strict_no_hypothesis");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "`===` with no hypothesis must NOT verify, got {result:?}"
    );
}

/// Adversarial #2: `=~=` over not-extensionally-equal sets must fail at the
/// `=~=` step, so the function as a whole must not verify (and the trailing
/// `===` must never become available).
#[test]
fn false_extensional_eq_fails_and_does_not_unlock_strict_eq() {
    let combined = verify("false_exteq_then_strict");
    assert!(
        !matches!(combined, VerifyResult::Verified),
        "a false `=~=` followed by `===` must NOT verify, got {combined:?}"
    );

    // Attribute the failure to the `=~=` obligation itself, in isolation.
    let exteq_only = verify("false_exteq_only");
    assert!(
        !matches!(exteq_only, VerifyResult::Verified),
        "`=~=` over not-extensionally-equal sets must fail at the `=~=` step, got {exteq_only:?}"
    );
}
