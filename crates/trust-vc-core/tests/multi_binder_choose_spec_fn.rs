// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression: a MULTI-BINDER `choose|i, j| P(i, j)` over an OPAQUE / spec-fn
//! predicate `P` must discharge the witness.
//!
//! The multi-binder choose lowers to a per-field decomposition
//! (`chosen_i = choose i. exists j. P(i, j)`, `chosen_j = choose j. P(chosen_i, j)`),
//! which reliably handles DIRECT / arithmetic predicates — each field's inner
//! `exists` Skolemizes to a ground witness that instantiates the next field's
//! choice. But for an opaque spec-fn `P`, that nested-`exists` trigger cannot
//! instantiate (its natural trigger binds the inner existential), so
//! `test1_tuple`/regression_1183-style goals were left `unknown`.
//!
//! The lowering now attaches the derivable combined axiom
//! `forall i, j. P(i, j) ==> P(chosen_i, chosen_j)` (a theorem of the per-field
//! Skolem axioms — if any tuple satisfies `P`, the jointly-chosen one does) to
//! the last per-field choose. Its scalar `P(i, j)` trigger matches a surrounding
//! `exists i, j. P(i, j)` Skolem, discharging the choice for the spec-fn case
//! while leaving the direct-predicate, extensionality, and soundness behavior
//! unchanged.
//!
//! Guards check BOTH directions: a witness-implied claim over a spec-fn verifies,
//! and claims that do NOT follow from the choice (a contradiction, or pinning the
//! chosen value to an arbitrary constant) still fail closed.

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/multi_binder_choose_spec_fn");
    fs::create_dir_all(dir).unwrap();
    let mut h = DefaultHasher::new();
    code.hash(&mut h);
    let f = dir.join(format!("{name}_{:016x}.rs", h.finish()));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

fn verified(r: &TrustVcResult<VerifyResult>) -> bool {
    matches!(r, Ok(VerifyResult::Verified))
}

const PRELUDE: &str = r#"
use trust_vc_types::{int};
#[trust_vc::spec]
fn lt(x: int, y: int) -> bool { x < y }
#[trust_vc::spec]
fn rel(i: int, j: int) -> bool { i <= j }
"#;

fn src(body: &str) -> String {
    format!("{PRELUDE}\n#[trust_vc::ensures(true)]\nfn test() {{\n{body}\n}}\n")
}

#[test]
fn multi_binder_choose_over_spec_fn_with_assumed_existence_verifies() {
    // `exists i, j. lt(i, j)` is assumed, so the chosen pair satisfies `lt`.
    let code = src("    trust_vc::assume!(exists|i: int, j: int| lt(i, j));\n\
         \x20   let (a, b): (int, int) = trust_vc::choose!(|i: int, j: int| lt(i, j));\n\
         \x20   trust_vc::assert!(lt(a, b));");
    let r = verify(&code, "test");
    assert!(
        verified(&r),
        "multi-binder choose over a spec-fn predicate should discharge the witness, got {r:?}"
    );
}

#[test]
fn multi_binder_choose_test1_tuple_shape_verifies() {
    // Mirrors choose.rs `test1_tuple::test_choose`: assume the relation is
    // inhabited, then assert the chosen pair satisfies it.
    let code = src("    trust_vc::assume!(exists|i: int, j: int| rel(i, j));\n\
         \x20   let (i, j): (int, int) = trust_vc::choose!(|i: int, j: int| rel(i, j));\n\
         \x20   trust_vc::assert!(rel(i, j));");
    let r = verify(&code, "test");
    assert!(
        verified(&r),
        "test1_tuple-shaped multi-binder choose over a spec-fn should verify, got {r:?}"
    );
}

#[test]
fn multi_binder_choose_over_spec_fn_contradiction_fails_closed() {
    // SOUNDNESS: `lt(b, a)` does NOT follow from `lt(a, b)`; must not verify.
    let code = src("    trust_vc::assume!(exists|i: int, j: int| lt(i, j));\n\
         \x20   let (a, b): (int, int) = trust_vc::choose!(|i: int, j: int| lt(i, j));\n\
         \x20   trust_vc::assert!(lt(b, a));");
    let r = verify(&code, "test");
    assert!(
        !verified(&r),
        "a claim contradicting the choose witness constraint must fail closed, got {r:?}"
    );
}

#[test]
fn multi_binder_choose_over_spec_fn_arbitrary_value_fails_closed() {
    // SOUNDNESS: the combined axiom gives `rel(a, b)`, NOT any specific value of
    // `a`; pinning `a == 7` must not verify (this is choose.rs `test1_fails2`).
    let code = src("    trust_vc::assume!(exists|i: int, j: int| rel(i, j));\n\
         \x20   let (a, _b): (int, int) = trust_vc::choose!(|i: int, j: int| rel(i, j));\n\
         \x20   trust_vc::assert!(a == 7);");
    let r = verify(&code, "test");
    assert!(
        !verified(&r),
        "pinning the chosen value to an arbitrary constant must fail closed, got {r:?}"
    );
}
