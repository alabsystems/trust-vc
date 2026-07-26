// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Soundness regression: a recursive spec function with no `#[decreases]`
//! termination proof must never let the engine prove a false statement.
//!
//! See encoder/verification/setup_broadcasts.rs (recursive body-axiom branch)
//! and encoder/fuel.rs (`encode_fuel_axioms`).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/recursive_axiom_soundness_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

#[test]
fn recursive_spec_fn_without_decreases_must_not_prove_false() {
    let path = repro_path();
    let verdict = verify_function_from_file(&path, "repro_proves_false")
        .expect("repro function should extract and verify");
    println!("repro_proves_false verdict: {verdict:?}");
    assert!(
        !matches!(verdict, VerifyResult::Verified),
        "UNSOUND: a false statement verified via an unguarded recursive defining \
         axiom (no decreases proof discharged). Verdict: {verdict:?}"
    );
}

#[test]
fn control_plainly_false_assertion_does_not_verify() {
    let path = repro_path();
    let verdict = verify_function_from_file(&path, "control_false_without_axiom")
        .expect("control function should extract and verify");
    println!("control_false_without_axiom verdict: {verdict:?}");
    assert!(
        !matches!(verdict, VerifyResult::Verified),
        "control: 1 == 2 must not verify; got {verdict:?}"
    );
}
