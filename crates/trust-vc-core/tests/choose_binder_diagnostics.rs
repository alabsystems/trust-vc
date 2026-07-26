// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verus-parity diagnostics for choose.rs #2777 cluster 6.
//!
//! Two upstream `choose.rs` tests assert that specific INVALID forms are
//! rejected with a specific message:
//!   * `test1_choose_with_closure_illegal`: a parenthesized binder
//!     `choose(|i, j| ..)` (call form) — "forall, choose, and exists do not
//!     allow parentheses". Only the bare `choose|..|` form is legal in Verus.
//!   * `test1_choose_tuple_wrong_type`: `let (i, j): (int, nat) =
//!     choose_tuple(|i: int, j: int| ..)` — "expected choose_tuple to have type"
//!     (the binder tuple is `(int, int)`, not `(int, nat)`).
//!
//! trust-vc previously accepted (and even proved) both — too permissive. It now
//! rejects them, fail-closed, with the upstream message. These tests guard both
//! the rejection AND that the LEGAL neighboring forms (`choose!` macro, a
//! matching-type `choose_tuple`) are unaffected.

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/choose_binder_diagnostics");
    fs::create_dir_all(dir).unwrap();
    let mut h = DefaultHasher::new();
    code.hash(&mut h);
    let f = dir.join(format!("{name}_{:016x}.rs", h.finish()));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

const PRELUDE: &str = r#"
use trust_vc_types::{int, nat};
#[trust_vc::spec]
fn f(i: int, j: int) -> bool { i <= j }
"#;

fn wrap(body: &str) -> String {
    format!("{PRELUDE}\n#[trust_vc::ensures(true)]\nfn test() {{\n{body}\n}}\n")
}

/// The error message returned (empty string if the call did not error).
fn err_message(r: &TrustVcResult<VerifyResult>) -> String {
    match r {
        Err(e) => e.to_string(),
        Ok(VerifyResult::Error { message }) => message.clone(),
        _ => String::new(),
    }
}

#[test]
fn parenthesized_choose_binder_is_rejected_with_verus_message() {
    let code = wrap("    let (i, j): (int, int) = choose(|i: int, j: int| f(i, j));");
    let r = verify(&code, "test");
    assert!(
        err_message(&r).contains("forall, choose, and exists do not allow parentheses"),
        "parenthesized choose must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn parenthesized_forall_binder_is_rejected() {
    let code = wrap("    let _b: bool = forall(|i: int| f(i, i));");
    let r = verify(&code, "test");
    assert!(
        err_message(&r).contains("forall, choose, and exists do not allow parentheses"),
        "parenthesized forall must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn choose_tuple_wrong_type_is_rejected_with_verus_message() {
    let code = wrap("    let (i, j): (int, nat) = choose_tuple(|i: int, j: int| f(i, j));");
    let r = verify(&code, "test");
    assert!(
        err_message(&r).contains("expected choose_tuple to have type"),
        "choose_tuple with a mismatched ascription must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn legal_choose_macro_in_let_is_not_rejected() {
    // The legal binder-in-let form is the `choose!` MACRO — must still verify.
    let code = wrap(
        "    trust_vc::assume!(exists|i: int, j: int| f(i, j));\n\
         \x20   let (a, b): (int, int) = trust_vc::choose!(|i: int, j: int| f(i, j));\n\
         \x20   trust_vc::assert!(f(a, b));",
    );
    let r = verify(&code, "test");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "the legal choose! macro form must not be caught by the parens diagnostic, got {r:?}"
    );
}

#[test]
fn choose_tuple_matching_type_is_not_rejected() {
    // A matching ascription must NOT trigger the wrong-type diagnostic.
    let code = wrap("    let (i, j): (int, int) = choose_tuple(|i: int, j: int| f(i, j));");
    let r = verify(&code, "test");
    assert!(
        !err_message(&r).contains("expected choose_tuple to have type"),
        "a matching-type choose_tuple must not be rejected, got {r:?}"
    );
}
