// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial soundness regression for Phase C closure-contract REFLECTION:
//! `f.requires((a,))` / `f.ensures((a,), r)` over a KNOWN LOCAL
//! `trust_vc::closure!` literal, lowered to the OPAQUE, DISJOINT UF predicates
//! `call_requires%` / `call_ensures%` and axiomatized from the WRITTEN contract.
//!
//! CARDINAL INVARIANT (closure edition): the reflection axiom is a DEFINITIONAL
//! equality (`call_requires%(f, q..) == R[q]`, `call_ensures%(f, q.., r) ==
//! E[q, r]`) over a FRESH symbol that appears nowhere else. A definitional
//! equality over a fresh symbol is a CONSERVATIVE EXTENSION:
//!   * it can NEVER inject inconsistency — a `requires(false)` closure publishes
//!     `call_requires%(f, q) == false` (the constant-false predicate), NOT the
//!     bare hypothesis `false`, so it cannot rescue an unrelated obligation;
//!   * it can NEVER let a caller read a false ensures as an ESTABLISHED fact —
//!     the equality fixes the UF's VALUE, saying nothing about the closure's
//!     actual behaviour. Direct application is deferred, so `call_ensures%`
//!     never connects to a real return value.
//! The INDEPENDENT def-side obligation (co-emitted, poison-probe-gated,
//! isolated child context) forces the body to back the ensures, so a lying
//! closure fails the whole function.
//!
//! Extraction may itself fail closed (capture guard / deferred application);
//! `assert_not_verified` treats an extraction `Err` as a sound non-verify, and
//! any solver `Unknown` counts as a FAILURE (never evidence).
//!
//! See `vc_extraction/body_extract.rs::emit_closure_reflection_axioms`,
//! `ir_builder::{call_requires,call_ensures}`, and the def-side companion suite
//! `closure_spec_soundness.rs`.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/closure_reflection_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> VerifyResult {
    verify_function_from_file(&repro_path(), func)
        .unwrap_or_else(|e| panic!("extract+verify `{func}` failed: {e:?}"))
}

fn assert_not_verified(func: &str) {
    match verify_function_from_file(&repro_path(), func) {
        Ok(VerifyResult::Verified) => {
            panic!("CLOSURE-REFLECTION FALSE-VERIFY: `{func}` must not verify")
        }
        // An extraction Err (capture guard / deferred application) is a sound
        // non-verify; a solver non-Verified verdict likewise.
        _ => {}
    }
}

#[test]
fn probe1_lying_ensures_reflection_counterexamples() {
    // THE cardinal unchecked-closure probe: the def-side COUNTEREXAMPLES; the
    // reflection read of `100 == 100` never rescues it.
    assert_not_verified("probe_lying_ensures_reflection_cx");
}

#[test]
fn probe2_reflection_over_valid_closure_verifies() {
    // The increment's success signal: verifies ONLY if the reflection axioms are
    // wired AND the def-side passes. A solver `Unknown` here is a FAILURE.
    let v = verdict("probe_reflection_verified");
    assert!(
        matches!(v, VerifyResult::Verified),
        "reflection over a def-side-valid closure should verify; got {v:?}"
    );
}

#[test]
fn probe3_bad_requires_reflection_counterexamples() {
    let v = verdict("probe_reflection_bad_requires_cx");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "a false requires reflection should counterexample; got {v:?}"
    );
}

#[test]
fn probe4_capture_reflection_fails_closed() {
    assert_not_verified("probe_capture_reflection_fail_closed");
}

#[test]
fn probe5_bare_closure_reflection_has_no_axiom() {
    assert_not_verified("probe_reflection_control_no_axiom");
}

#[test]
fn probe6_loop_body_reflection_axiom_is_dropped() {
    // Discipline: the loop-body axiom is DROPPED, so the in-loop reflection
    // assert cannot be discharged — no verified-by-leak.
    assert_not_verified("probe_reflection_loop_drop_fails_closed");
}

#[test]
fn probe7_direct_application_now_verifies() {
    // Phase C part 2 FLIP: direct application `f(2)` of a UNARY closure! literal
    // now lowers to the shared `spec_fn_apply` UF, with the call-site seam proving
    // requires and assuming the def-side-checked ensures. Formerly pinned as
    // "still deferred". A solver `Unknown` here is a FAILURE. (The n-ary /
    // bare-closure deferred pins live in `closure_direct_application_soundness.rs`.)
    let v = verdict("probe_direct_application_now_verifies");
    assert!(
        matches!(v, VerifyResult::Verified),
        "unary direct application of a def-side-valid closure! should verify; got {v:?}"
    );
}

#[test]
fn probe8_unmodelable_param_closure_stays_deferred() {
    assert_not_verified("probe_unmodelable_param_closure_stays_deferred");
}

#[test]
fn probe9_false_ensures_reflection_is_not_an_established_fact() {
    let v = verdict("probe_reflection_false_ensures_not_a_fact");
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "a wrong ensures reflection value should counterexample; got {v:?}"
    );
}
