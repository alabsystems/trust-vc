// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `unsafe` on a non-exec function, rejected at SIGNATURE lowering.
//!
//! Upstream parity target: `rust_verify_test/tests/unsafe.rs` —
//! `unsafe_proof_fn_fail` (rejected with the verbatim message) and
//! `unsafe_fns_ok` (an `unsafe` EXEC fn, accepted).
//!
//! The rule must be answerable WITHOUT a contract to extract, because the
//! evidence gate's per-function lane skips a contract-free function before it
//! ever reaches `extract_verification_conditions`. That lane is the reason
//! `static_signature_rejection` exists: before it, the gate supplied this
//! diagnostic itself, from its own syn scan, and the proof calculus never ran.

use crate::static_signature_rejection;

const UPSTREAM_MESSAGE: &str = "'unsafe' only makes sense on exec-mode functions";

#[test]
fn proof_unsafe_fn_is_rejected_without_any_contract() {
    let source = r#"
#[trust_vc::proof]
unsafe fn unsafe_proof_fn_fail() {}
"#;
    assert_eq!(
        static_signature_rejection(source, "unsafe_proof_fn_fail").as_deref(),
        Some(UPSTREAM_MESSAGE)
    );
}

#[test]
fn spec_unsafe_fn_is_rejected() {
    let source = r#"
#[trust_vc::spec]
unsafe fn spec_unsafe() -> bool { true }
"#;
    assert_eq!(
        static_signature_rejection(source, "spec_unsafe").as_deref(),
        Some(UPSTREAM_MESSAGE)
    );
}

#[test]
fn exec_unsafe_fn_is_accepted() {
    let source = r#"
#[trust_vc::ensures(true)]
unsafe fn unsafe_fns_ok() {}
"#;
    assert_eq!(static_signature_rejection(source, "unsafe_fns_ok"), None);
}

#[test]
fn safe_proof_fn_is_accepted() {
    let source = r#"
#[trust_vc::proof]
fn safe_proof() {}
"#;
    assert_eq!(static_signature_rejection(source, "safe_proof"), None);
}

#[test]
fn proof_unsafe_fn_inside_a_module_is_rejected() {
    let source = r#"
mod inner {
    #[trust_vc::proof]
    unsafe fn nested_unsafe_proof() {}
}
"#;
    assert_eq!(
        static_signature_rejection(source, "nested_unsafe_proof").as_deref(),
        Some(UPSTREAM_MESSAGE)
    );
}

#[test]
fn an_unknown_function_name_yields_no_rejection() {
    let source = r#"
#[trust_vc::proof]
unsafe fn unsafe_proof_fn_fail() {}
"#;
    assert_eq!(static_signature_rejection(source, "not_here"), None);
}
