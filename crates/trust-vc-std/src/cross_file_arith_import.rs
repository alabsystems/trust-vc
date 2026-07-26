//! Cross-file opacity tests for the opaque `arithmetic::{mul, add, sub}` spec
//! functions, imported ACROSS a file boundary.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These mirror the in-file `arithmetic::opaque_arith` tests (commit `de061ac`)
//! but exercise the *cross-file* import path: the `#[trust_vc::spec]
//! #[trust_vc::opaque]` definitions of `mul` / `add` / `sub` live in
//! `crate::arithmetic` (a sibling module, a DIFFERENT source file), and are
//! brought into this verified file's scope by a `use crate::arithmetic::{…}`
//! import. The spec catalog must (a) discover the crate root from this file's
//! path, (b) walk the crate to find the imported defs in `arithmetic.rs`, and
//! (c) register them under their imported names — all while preserving opacity.
//!
//! The differential checks are identical to the in-file suite, which is the
//! point: resolving an import across files must not change the semantics.
//!
//! * opaque-by-default: `mul(2, 3) == 6` is REJECTED (the body axiom is hidden);
//! * after `reveal!(mul)`: `mul(2, 3) == 6` VERIFIES;
//! * SOUNDNESS: a revealed-but-FALSE goal (`mul(2, 3) == 7`) is REJECTED — the
//!   import never fabricates a value, and never lets a false goal pass;
//! * reveal is exact across files: `reveal!(mul)` does not disclose `add`.

use crate::arithmetic::{add, mul, sub};

/// Runs a `#[trust_vc::proof]` function with clean thread-local verification
/// state, returning `Err(panic message)` when the proof is rejected (the
/// `#[proof]` auto-verify boundary panics on a non-`Verified` outcome) and
/// `Ok(())` when it verifies.
fn run_proof<F: FnOnce() + std::panic::UnwindSafe>(proof_fn: F) -> Result<(), String> {
    clear_state();
    let outcome = std::panic::catch_unwind(proof_fn);
    clear_state();
    outcome.map_err(|payload| {
        payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_string()))
            .unwrap_or_else(|| "unknown panic".to_string())
    })
}

fn clear_state() {
    trust_vc_core::verify_macro::clear_all_thread_locals();
    trust_vc_core::verification_bridge::clear_registrations();
    trust_vc_core::clear_extern_contracts();
}

fn assert_verifies<F: FnOnce() + std::panic::UnwindSafe>(proof_fn: F) {
    if let Err(msg) = run_proof(proof_fn) {
        panic!("expected proof to verify, but it was rejected: {msg}");
    }
}

fn assert_rejected<F: FnOnce() + std::panic::UnwindSafe>(proof_fn: F) {
    match run_proof(proof_fn) {
        Ok(()) => panic!("expected proof to be rejected (opaque body hidden), but it verified"),
        Err(msg) => {
            // The rejection MUST be a genuine non-`Verified` verdict
            // (Counterexample / Unknown), NOT an infrastructure/context error.
            // Otherwise a malformed signature could make the proof "fail" for the
            // wrong reason and mask a real opacity break (or a resolution break
            // that silently leaves the symbol uninterpreted for a bad reason).
            let genuine = msg.contains("Proof verification failed")
                || msg.contains("Proof verification returned Unknown");
            assert!(
                genuine,
                "proof was rejected, but NOT by a genuine verification verdict \
                 (possible infrastructure error): {msg}"
            );
        }
    }
}

// --- Opaque-by-default across files: hidden body cannot discharge values. ---

#[trust_vc::proof]
fn imported_mul_without_reveal_is_hidden() {
    let _ = mul(2, 3);
    trust_vc::assert!(mul(2, 3) == 6);
}

#[trust_vc::proof]
fn imported_add_without_reveal_is_hidden() {
    let _ = add(2, 3);
    trust_vc::assert!(add(2, 3) == 5);
}

#[trust_vc::proof]
fn imported_sub_without_reveal_is_hidden() {
    let _ = sub(5, 3);
    trust_vc::assert!(sub(5, 3) == 2);
}

// --- Revealed across files: defining body axiom evaluates concrete args. ---

#[trust_vc::proof]
fn imported_mul_with_reveal_verifies() {
    let _ = mul(2, 3);
    trust_vc::reveal!(mul);
    trust_vc::assert!(mul(2, 3) == 6);
}

#[trust_vc::proof]
fn imported_add_with_reveal_verifies() {
    let _ = add(2, 3);
    trust_vc::reveal!(add);
    trust_vc::assert!(add(2, 3) == 5);
}

#[trust_vc::proof]
fn imported_sub_with_reveal_verifies() {
    let _ = sub(5, 3);
    trust_vc::reveal!(sub);
    trust_vc::assert!(sub(5, 3) == 2);
}

// --- Soundness: revealing the correct body must NOT prove a false goal. ---

#[trust_vc::proof]
fn imported_mul_revealed_false_goal_is_rejected() {
    let _ = mul(2, 3);
    trust_vc::reveal!(mul);
    trust_vc::assert!(mul(2, 3) == 7);
}

// --- Reveal is exact across files: revealing `mul` leaves `add` opaque. ---

#[trust_vc::proof]
fn imported_reveal_mul_does_not_reveal_add() {
    let _ = mul(2, 3);
    let _ = add(2, 3);
    trust_vc::reveal!(mul);
    trust_vc::assert!(add(2, 3) == 5);
}

#[test]
fn imported_opaque_arithmetic_without_reveal_stays_hidden() {
    assert_rejected(imported_mul_without_reveal_is_hidden);
    assert_rejected(imported_add_without_reveal_is_hidden);
    assert_rejected(imported_sub_without_reveal_is_hidden);
}

#[test]
fn imported_opaque_arithmetic_with_reveal_evaluates() {
    assert_verifies(imported_mul_with_reveal_verifies);
    assert_verifies(imported_add_with_reveal_verifies);
    assert_verifies(imported_sub_with_reveal_verifies);
}

#[test]
fn imported_revealed_arithmetic_rejects_false_goal() {
    assert_rejected(imported_mul_revealed_false_goal_is_rejected);
}

#[test]
fn imported_reveal_is_exact_per_function() {
    assert_rejected(imported_reveal_mul_does_not_reveal_add);
}
