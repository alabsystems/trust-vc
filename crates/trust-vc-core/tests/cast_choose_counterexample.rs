//! Regression tests for the cast-`choose` counterexample fix (ay
//! `quantifier_is_total_true_bool_predicate`, ay main ce694041dc).
//!
//! Upstream `choose.rs::test_refine_fail1` shape:
//!   `(choose|n: nat| cintf(n as int) && n < 0) < 0`   with `cintf ≡ true`.
//! The choose ranges over the EMPTY nat set (no nat `n` has `n < 0`), so the
//! Hilbert value is an arbitrary `nat >= 0` and `< 0` is false => Counterexample.
//!
//! Before the fix the `n as int` cast seeded `-1` into ay's MBQI candidate
//! synthesis; the spec-fn definitional axiom `∀x. cintf(x)` (body ≡ true) had
//! its `(cintf -1)` instance judged `incomplete` (the UF-completion recognizers
//! required an `=`-headed body), degrading the skipped-quantifier soundness gate
//! to Unknown and discarding the finalize-validated CE. The new recognizer treats
//! `∀v⃗. f(v⃗)` as the total definition `f ≡ true`, so the CE is now reported.
//!
//! SOUNDNESS: the gate only ever accepts a SAT model as a Counterexample or
//! degrades to Unknown (it never emits Unsat), so this cannot be a false-verify.
//! The adversarial `cast_verify` case pins that a genuinely-valid `>= 0` claim —
//! where the SAME recognizer fires — stays Verified, not a spurious CE.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::Path;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(code: &str) -> VerifyResult {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/cast_choose_counterexample");
    fs::create_dir_all(dir).unwrap();
    let mut h = DefaultHasher::new();
    code.hash(&mut h);
    let f = dir.join(format!("t_{:016x}.rs", h.finish()));
    fs::write(&f, code).unwrap();
    verify_function_from_file(f.to_str().unwrap(), "test").expect("extract")
}

const PRELUDE: &str = r#"
use trust_vc_types::{int, nat};
#[trust_vc::spec]
fn cintf(n: int) -> bool { true }
"#;

fn func(body: &str) -> String {
    format!("{PRELUDE}\n#[trust_vc::ensures(true)]\nfn test() {{\n{body}\n}}\n")
}

// ---- the fix: cast choose over an empty nat set, false `< 0` claim => CE ----

#[test]
fn cast_choose_empty_set_negative_false_claim_is_counterexample() {
    let r = verify(&func(
        "    let n: nat = trust_vc::choose!(|n: nat| cintf(n as int) && n < 0);\n\
         \x20   trust_vc::assert!(n < 0);",
    ));
    assert!(
        matches!(r, VerifyResult::Counterexample { .. }),
        "expected Counterexample (choose over empty nat set is >= 0), got {r:?}"
    );
}

// ---- adversarial: same recognizer fires, but the `>= 0` claim is VALID ----

#[test]
fn cast_choose_nonnegative_claim_verifies_not_false_ce() {
    // Any nat is >= 0, so this is genuinely valid; the total-true `cintf`
    // recognizer fires here too, and MUST NOT turn a valid claim into a CE.
    let r = verify(&func(
        "    let n: nat = trust_vc::choose!(|n: nat| cintf(n as int) && n < 0);\n\
         \x20   trust_vc::assert!(n >= 0);",
    ));
    assert!(
        matches!(r, VerifyResult::Verified),
        "expected Verified (nat is always >= 0), got {r:?}"
    );
}
