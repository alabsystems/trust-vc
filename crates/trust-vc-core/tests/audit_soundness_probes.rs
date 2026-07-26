// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Regression probes from the 2026-07-20 adversarial pattern/if-let soundness
//! audit. The three pattern-refinement-DROP cases were confirmed false-verifies
//! (fixed: match_lowering const-pattern fail-close + body_extract tuple-struct/
//! struct refinement guard); the if-let shape probes confirm the if-let->match
//! desugar stays sound on or-pattern / nested / call-scrutinee / literal shapes.
//! Targets MUST fail closed (never Verified); controls MUST verify.

use trust_vc_core::{verify_function_from_file, VerifyResult};
fn fx(n: &str) -> String {
    format!("{}/tests/data/{n}", env!("CARGO_MANIFEST_DIR"))
}
fn not_verified(file: &str, f: &str) {
    let v = verify_function_from_file(&fx(file), f);
    eprintln!("[TARGET] {f} => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: {f} in {file}"
    );
}
fn verifies(file: &str, f: &str) {
    let v = verify_function_from_file(&fx(file), f);
    eprintln!("[CONTROL] {f} => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "control should verify: {f} => {v:?}"
    );
}

// --- pattern-refinement DROP false-verifies (FIXED) ---
#[test]
fn tuple_struct_payload_literal_not_dropped() {
    not_verified(
        "audit_probe_9.rs",
        "payload_literal_refinement_must_not_drop",
    );
    verifies("audit_probe_9.rs", "payload_true_assert_verifies");
}
#[test]
fn const_pattern_not_collapsed_to_binding() {
    not_verified(
        "audit_probe_10.rs",
        "const_pattern_refinement_must_not_drop",
    );
    verifies("audit_probe_10.rs", "plain_binding_is_irrefutable");
}
#[test]
fn struct_field_literal_not_dropped() {
    not_verified(
        "audit_probe_11.rs",
        "struct_field_literal_refinement_must_not_drop",
    );
    verifies("audit_probe_11.rs", "struct_field_true_assert_verifies");
}

// --- if-let desugar stays sound on more shapes (targets fail closed / CX) ---
#[test]
fn if_let_or_pattern_sound() {
    not_verified("audit_probe_5.rs", "if_let_or_pattern_must_cx");
}
#[test]
fn if_let_nested_sound() {
    not_verified("audit_probe_6.rs", "if_let_nested_must_cx");
}
#[test]
fn if_let_call_scrutinee_sound() {
    not_verified("audit_probe_7.rs", "if_let_call_scrutinee_must_cx");
    verifies("audit_probe_7.rs", "if_let_call_scrutinee_positive");
}
#[test]
fn if_let_literal_sound() {
    not_verified("audit_probe_8.rs", "if_let_literal_must_cx");
}
