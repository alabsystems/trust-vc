//! Regression tests for definitional-equality-`choose` recognition (Fix B).
//!
//! When a `choose` predicate is a definitional equality `binder == g` (with `g`
//! free of the binder and the binder type having reflexive-total `==`), the
//! Hilbert choice is definitionally `g`, so the encoder asserts the ground fact
//! `choose_result == g` and skips the (redundant, and for bit-vectors unhandled)
//! guarded axiom. This makes such chooses verify/counterexample deterministically
//! instead of returning a context-dependent `quantifier-unhandled` Unknown.
//!
//! These tests pin BOTH the new capability AND its soundness guards — a wrong
//! `g`-free-of-binder check or a missing type restriction would be a false-verify
//! (the cardinal sin), so they are exercised explicitly.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::Path;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(code: &str) -> VerifyResult {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/definitional_equality_choose");
    fs::create_dir_all(dir).unwrap();
    let mut h = DefaultHasher::new();
    code.hash(&mut h);
    let f = dir.join(format!("t_{:016x}.rs", h.finish()));
    fs::write(&f, code).unwrap();
    verify_function_from_file(f.to_str().unwrap(), "test").expect("extract")
}

const PRELUDE: &str = r#"
use trust_vc_types::int;
#[trust_vc::spec]
fn f(i: int) -> bool { 5 <= i }
"#;

fn with_param(body: &str) -> String {
    format!("{PRELUDE}\n#[trust_vc::ensures(true)]\nfn test(c: int) {{\n{body}\n}}\n")
}
fn no_param(body: &str) -> String {
    format!("{PRELUDE}\n#[trust_vc::ensures(true)]\nfn test() {{\n{body}\n}}\n")
}

// ---- capability: `choose|i| c == i` is definitionally `c` ----

#[test]
fn definitional_eq_false_claim_is_counterexample() {
    // choose i with (c == i) IS c, so `i != c` is false => Counterexample.
    let r = verify(&with_param(
        "    let i: int = trust_vc::choose!(|i: int| c == i);\n    trust_vc::assert!(i != c);",
    ));
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "expected Counterexample, got {r:?}"
    );
}

#[test]
fn definitional_eq_true_claim_verifies() {
    let r = verify(&with_param(
        "    let i: int = trust_vc::choose!(|i: int| c == i);\n    trust_vc::assert!(i == c);",
    ));
    assert!(
        matches!(r, VerifyResult::Verified),
        "expected Verified, got {r:?}"
    );
}

#[test]
fn definitional_eq_reversed_operands_verifies() {
    // binder on the left: `i == c`.
    let r = verify(&with_param(
        "    let i: int = trust_vc::choose!(|i: int| i == c);\n    trust_vc::assert!(i == c);",
    ));
    assert!(
        matches!(r, VerifyResult::Verified),
        "expected Verified, got {r:?}"
    );
}

// ---- SOUNDNESS GUARD: `g` mentions the binder => NOT definitional ----

#[test]
fn self_referential_equality_is_not_definitional() {
    // `i == i + 1` is unsatisfiable, so the choose is arbitrary; the encoder must
    // NOT treat it as definitional (which would assert the false `result == i+1`).
    // The claim `i == i + 1` must therefore NOT verify (must be non-Verified).
    let r = verify(&with_param(
        "    let _ = c;\n    let i: int = trust_vc::choose!(|i: int| i == i + 1);\n    trust_vc::assert!(i == i + 1);",
    ));
    assert!(
        !matches!(r, VerifyResult::Verified),
        "self-referential equality must not false-verify, got {r:?}"
    );
}

// ---- SOUNDNESS GUARD: the STEP-3 witnessless spec-fn choose still counters ----

#[test]
fn witnessless_spec_fn_choose_still_counterexample() {
    // Not a definitional equality; the no_mbqi guarded-axiom path must be
    // untouched by Fix B: a witnessless spec-fn choose stays a Counterexample
    // (never Verified).
    let r = verify(&no_param(
        "    let i: int = trust_vc::choose!(|i: int| f(i));\n    trust_vc::assert!(f(i));",
    ));
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "witnessless spec-fn choose must be a Counterexample, got {r:?}"
    );
}
