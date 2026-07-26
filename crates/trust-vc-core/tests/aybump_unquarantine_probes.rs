// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial re-verification of the two SOLVER-DEPENDENT un-quarantined
//! foundations under ay pin 4df6ab25 — the closure def-side isolation lane and
//! the `loop_decreases!` WF1 non-negativity floor. Each fresh probe injects a
//! `forall` into exactly the query the ay bump's `forall_inst` /
//! quantified-refutation delta (a998c3e3 -> 4df6ab25) would perturb, and must
//! still fail closed. Positive controls prove the probes are load-bearing (not
//! passing on a parse/extraction failure).
//!
//! (The other two un-quarantined lanes — a2-generic-inherent and broadcast_use —
//! are solver-INDEPENDENT by construction: their guards are registry-build /
//! trust-vc-side and ay cannot perturb them; they stay covered by
//! `a2_generic_soundness` and `broadcast_use_soundness`.)

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fixture(name: &str) -> String {
    format!("{}/tests/data/{name}", env!("CARGO_MANIFEST_DIR"))
}

fn assert_not_verified(file: &str, function: &str) {
    let v = verify_function_from_file(&fixture(file), function);
    eprintln!("[PROBE] {function} => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "AY-BUMP BREACH: `{function}` from `{file}` must fail closed, got Verified"
    );
}

fn assert_verified(file: &str, function: &str) {
    let v = verify_function_from_file(&fixture(file), function);
    eprintln!("[CONTROL] {function} => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "CONTROL REGRESSION: `{function}` from `{file}` should verify, got {v:?}"
    );
}

/// Closure def-side isolation vs `forall_inst`: a closure whose `requires` is a
/// QUANTIFIED contradiction (`forall k. k < 5`) must not leak into the parent
/// and let the parent's `assert!(false)` verify vacuously. Correct: Counterexample.
#[test]
fn closure_def_side_quantified_contradiction_fails_closed() {
    assert_not_verified(
        "closure_def_side_aybump_probe.rs",
        "quantified_requires_contradiction_cannot_poison_parent",
    );
}

/// Load-bearing control: a def-side-valid closure with a SATISFIABLE quantified
/// `requires` must still verify (proves the quantifier path is exercised, so the
/// probe above is not passing merely on a rejected `forall`).
#[test]
fn closure_def_side_valid_quantified_requires_verifies() {
    assert_verified(
        "closure_def_side_aybump_probe.rs",
        "def_side_quantified_requires_valid_verifies",
    );
}

/// `loop_decreases!` WF1 floor vs `forall_inst`: an unbounded-below `int`
/// measure whose floor query carries injected (tautological, bind-nothing)
/// `forall` facts must still be rejected by the non-negativity floor. Correct:
/// Counterexample (a spurious UNSAT leak from `forall_inst` would false-verify).
#[test]
fn loop_decreases_quantified_floor_fails_closed() {
    assert_not_verified("loop_decreases_aybump_probe.rs", "quantified_floor_probe");
}
