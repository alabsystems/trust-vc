// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CAPABILITY PIN: direct application of a closure literal bound to a local,
//! on the FILE-EXTRACTION path.
//!
//! Two capability-audit rows describe this area pessimistically:
//!
//!   * row 458 — "Direct application / beta reduction of spec closure literals
//!     (`let f = |x:int| x+1; assert(f(10)==11)`)" — scored **MISSING**, with
//!     "No value-level encoding of a closure literal bound to a local".
//!   * row 454 — exec closures — scored **PARTIAL**, with "the working
//!     `closure!` surface is unreachable from the file-extraction path the
//!     corpus/gate uses".
//!
//! Probed, and both are stale for this shape: a capture-free closure literal
//! bound to a local and applied is inlined at the call site and verifies through
//! `verify_function_from_file` — the same entry the corpus and gate use — while
//! a wrong postcondition over the identical body returns a counterexample.
//!
//! The liar cases are the point. A capability that verifies the true case but
//! cannot refute the false one is not a capability, it is a rubber stamp; these
//! tests fail if the discrimination is ever lost in either direction.
//!
//! Scope, stated so the rows are not over-corrected: this pins CAPTURE-FREE
//! literals applied directly. Captures, closures passed as arguments, and
//! closures with their own `requires`/`ensures` are NOT covered here and remain
//! genuinely open. Row 432/343's claim — that `decreases!()` is not consumable
//! on the file path — was probed in the same pass and is ACCURATE: it fails
//! closed with "Unsupported decreases!() in vc_extraction".

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(tmp_id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_cla_{}_{}.rs", std::process::id(), tmp_id));
    std::fs::write(&p, src).expect("write fixture");
    let result =
        verify_function_from_file(p.to_str().expect("utf8 path"), func).unwrap_or_else(|e| {
            VerifyResult::Error {
                message: e.to_string(),
            }
        });
    let _ = std::fs::remove_file(&p);
    result
}

const BETA: &str = r#"
#[trust_vc::ensures(result == 11u64)]
pub fn beta_true() -> u64 {
    let f = |x: u64| x + 1u64;
    f(10u64)
}

#[trust_vc::ensures(result == 999u64)]
pub fn beta_liar() -> u64 {
    let f = |x: u64| x + 1u64;
    f(10u64)
}
"#;

const MULTI_ARG: &str = r#"
#[trust_vc::ensures(result == 7u64)]
pub fn add_true() -> u64 {
    let add = |a: u64, b: u64| a + b;
    add(3u64, 4u64)
}

#[trust_vc::ensures(result == 8u64)]
pub fn add_liar() -> u64 {
    let add = |a: u64, b: u64| a + b;
    add(3u64, 4u64)
}
"#;

#[test]
fn closure_literal_beta_reduction_verifies_on_the_file_path() {
    let result = verify("beta_t", "beta_true", BETA);
    assert!(
        matches!(result, VerifyResult::Verified),
        "row 458 is scored MISSING, but `let f = |x| x + 1; f(10)` verifies: {result:?}"
    );
}

#[test]
fn closure_literal_beta_reduction_refutes_a_false_postcondition() {
    let result = verify("beta_l", "beta_liar", BETA);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "a false postcondition over an inlined closure body must be refuted, not \
         merely unproved — otherwise the capability is a rubber stamp: {result:?}"
    );
}

#[test]
fn multi_argument_closure_application_verifies_on_the_file_path() {
    let result = verify("add_t", "add_true", MULTI_ARG);
    assert!(
        matches!(result, VerifyResult::Verified),
        "row 454 says the closure surface is unreachable from file extraction, \
         but a two-argument literal applies and verifies: {result:?}"
    );
}

#[test]
fn multi_argument_closure_application_refutes_a_false_postcondition() {
    let result = verify("add_l", "add_liar", MULTI_ARG);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "the two-argument case must discriminate too: {result:?}"
    );
}
