// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression guard: a `forall`/`exists` body that references a LET-BOUND local
//! ACROSS a `==>` (implies) marker resolves and is soundly checked.
//!
//! Pre-fix, `let s = ..; assert!(forall|k| s.contains(k) ==> P)` failed to lower
//! with "unresolved variable `s`": `==>` is normalized to a `__trust_vc_implies!`
//! MARKER macro, and the scoped-substitution visitors do not descend into a
//! macro's opaque token stream, so the let-local inside the implies was never
//! substituted. The fix normalizes those markers to same-named CALL forms around
//! the (capture-avoiding) substitution, then denormalizes.
//!
//! The two load-bearing directions:
//!   * a GENUINELY-FALSE forall-implies over a let-bound collection must be
//!     REFUTED — never a false `Verified`, and no longer a fail-closed
//!     "unresolved variable" Error (it must actually reach the solver);
//!   * a GENUINELY-TRUE forall-implies over the SAME let-bound collection must
//!     still VERIFY — the marker substitution must not capture the bound var or
//!     otherwise fabricate a counterexample (the `p >= p` capture landmine).

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(name: &str, src: &str, target: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_fli_{}_{}.rs", std::process::id(), name));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), target).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}

// FALSE: s = {1,2}; k=1 ∈ s but 1 > 5 is false, so `forall k∈s. k>5` is false.
const FALSE_IMPLIES: &str = r#"
use trust_vc_types::Set;
#[trust_vc::ensures(true)]
fn false_forall_implies() {
    let s = Set::<int>::empty().insert(1int).insert(2int);
    trust_vc::assert!(forall|k: int| s.contains(k) ==> k > 5int);
}
"#;

// TRUE: s = {1,2}; every k ∈ s satisfies k >= 1, so the claim holds.
const TRUE_IMPLIES: &str = r#"
use trust_vc_types::Set;
#[trust_vc::ensures(true)]
fn true_forall_implies() {
    let s = Set::<int>::empty().insert(1int).insert(2int);
    trust_vc::assert!(forall|k: int| s.contains(k) ==> k >= 1int);
}
"#;

#[test]
fn false_forall_implies_over_let_collection_is_refuted() {
    let result = verify("false", FALSE_IMPLIES, "false_forall_implies");
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "a genuinely-false `forall|k| s.contains(k) ==> k > 5` over a let-bound Set must be \
         REFUTED (and must reach the solver — no 'unresolved variable `s`' Error); got: {result:?}"
    );
}

#[test]
fn true_forall_implies_over_let_collection_verifies() {
    let result = verify("true", TRUE_IMPLIES, "true_forall_implies");
    assert!(
        matches!(result, VerifyResult::Verified),
        "a genuinely-true `forall|k| s.contains(k) ==> k >= 1` over the SAME let-bound Set must \
         VERIFY — the implies-marker substitution must not fabricate a counterexample or capture \
         the bound var; got: {result:?}"
    );
}
