// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Set/Map extensional-equality precondition-consumption soundness guards.
//!
//! A precondition-dependent valid ext-eq lemma (e.g. `s.insert(x).remove(x)
//! =~= s` under `requires !s.contains(x)`) must VERIFY, while a
//! genuinely-different ext-eq (no forcing precondition, or a real differing
//! element) must still produce a COUNTEREXAMPLE, and a wrong-precondition
//! claim must still refute. Verified through `verify_function_from_file`,
//! mirroring the upstream maps.rs/sets.rs ports.

use std::path::PathBuf;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fixture_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/set_map_ext_eq_precond.rs")
}

fn verify(case: &str) -> VerifyResult {
    let path = fixture_path();
    verify_function_from_file(path.to_str().unwrap(), case)
        .unwrap_or_else(|err| panic!("{case} should extract: {err}"))
}

fn assert_verified(case: &str) {
    let r = verify(case);
    assert!(r.is_verified(), "{case}: expected Verified, got {r:?}");
}

fn assert_counterexample(case: &str) {
    let r = verify(case);
    assert!(
        r.is_counterexample(),
        "{case}: expected Counterexample, got {r:?}"
    );
}

// ── VALID precondition-dependent lemmas → Verified ─────────────────────────

#[test]
fn valid_set_insert_remove_exteq() {
    assert_verified("set_insert_remove_exteq");
}

#[test]
fn valid_set_insert_remove_eq() {
    assert_verified("set_insert_remove_eq");
}

#[test]
fn valid_set_remove_noop_exteq() {
    assert_verified("set_remove_noop_exteq");
}

#[test]
fn valid_set_insert_noop_exteq() {
    assert_verified("set_insert_noop_exteq");
}

#[test]
fn valid_map_insert_noop_exteq() {
    assert_verified("map_insert_noop_exteq");
}

// ── Decomposed + control (must Verify regardless) ──────────────────────────

#[test]
fn control_set_insert_remove_decomposed() {
    assert_verified("set_insert_remove_decomposed");
}

#[test]
fn control_set_insert_remove_eq_remove() {
    assert_verified("set_insert_remove_eq_remove");
}

// ── GENUINELY-DIFFERENT → Counterexample ───────────────────────────────────

#[test]
fn diff_set_insert_noop_no_precond() {
    assert_counterexample("set_insert_noop_no_precond");
}

#[test]
fn diff_map_insert_noop_no_precond() {
    assert_counterexample("map_insert_noop_no_precond");
}

#[test]
fn diff_set_remove_noop_no_precond() {
    assert_counterexample("set_remove_noop_no_precond");
}

#[test]
fn diff_set_concrete_different() {
    assert_counterexample("set_concrete_different");
}

#[test]
fn diff_map_concrete_different() {
    assert_counterexample("map_concrete_different");
}

// ── WRONG precondition → Counterexample ────────────────────────────────────

#[test]
fn wrong_precond_set_insert_remove() {
    assert_counterexample("set_insert_remove_wrong_precond");
}
