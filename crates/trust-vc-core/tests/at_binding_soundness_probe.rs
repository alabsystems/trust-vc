// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use trust_vc_core::{verify_function_from_file, VerifyResult};
fn fx(n: &str) -> String {
    format!("{}/tests/data/{n}", env!("CARGO_MANIFEST_DIR"))
}
#[test]
fn at_binding_refinement_must_not_drop() {
    let v = verify_function_from_file(
        &fx("at_binding_soundness_probe.rs"),
        "at_zero_refinement_must_not_drop",
    );
    eprintln!("[AT-PROBE] at_zero_refinement_must_not_drop => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: dropped `@ 0` refinement"
    );
}
#[test]
fn bare_binding_control_verifies() {
    let v = verify_function_from_file(
        &fx("at_binding_soundness_probe.rs"),
        "bare_binding_is_irrefutable",
    );
    eprintln!("[AT-CTRL] bare_binding_is_irrefutable => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "control should verify, got {v:?}"
    );
}
