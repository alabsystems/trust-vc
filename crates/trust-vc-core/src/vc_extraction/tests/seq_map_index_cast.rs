// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression: `Seq::map(f).index(k)` with a closure body that casts the index
//! (`i as i32`) must be DECIDED at a concrete index `k` on BOTH pointer-width
//! legs — `Verified` for the true value, `Counterexample` for a wrong one.
//!
//! Before the fix, the pointwise map axiom's index variable `bound_idx` was not
//! registered in a quantifier scope (the map builds its `forall` manually), so a
//! SAME-WIDTH index cast — `i as i32` when `pointer_width() == 32`, a 32-bit
//! `usize` reinterpreted to a 32-bit `i32` — routed through
//! `reinterpret_bv_signedness`'s FREE-term branch and minted a fresh
//! `sc == bound_idx` var. The ground seed discharges concrete-index goals by
//! `substitute(body_eq, [bound_idx], [k])`, which rewrites `bound_idx` but not the
//! disconnected `sc`, so `f(k, ..)` never folded and `result[k]` stayed
//! unconstrained — Unknown ONLY on `arch_32bit` (on 64-bit the cast is a
//! NARROWING `bvextract` that folds). Marking `bound_idx` quantifier-bound while
//! encoding the body routes the cast through the in-place path so the seed's
//! substitution reaches it. This is upstream `seqs.rs::test1`'s
//! `s6.index(2) == 34` (a `map(|i,a| 2*(i as i32)+a)` read).

use super::*;
use crate::encoder::VerifyResult;

fn verdict(code: &str, name: &str) -> VerifyResult {
    let file = parse_file(code).expect("fixture should parse");
    let func =
        find_function(&file, name).unwrap_or_else(|| panic!("fixture should define fn {name}"));
    extract_verification_conditions(func)
        .unwrap_or_else(|err| panic!("fn {name} should extract: {err}"))
        .verify()
}

fn assert_verified(code: &str, name: &str) {
    match verdict(code, name) {
        VerifyResult::Verified => {}
        other => {
            panic!("fn {name} should verify (map-index cast at concrete index), got: {other:?}")
        }
    }
}

/// A false `Verified` on an unequal claim would be the cardinal soundness
/// failure. Fail-closed (Counterexample/Unknown) is acceptable; `Verified` not.
fn assert_not_verified(code: &str, name: &str) {
    match verdict(code, name) {
        VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. } => {}
        VerifyResult::Verified => {
            panic!(
                "fn {name} must NOT verify (wrong map-index value) — a false Verified is unsound"
            )
        }
        other => panic!("fn {name} unexpected verdict: {other:?}"),
    }
}

/// `[10,20,30].map(|i,a| 2*(i as i32)+a).index(2) == 34`  (2*2 + 30 = 34).
#[test]
fn map_index_cast_true_value_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            trust_vc::assert!(
                trust_vc_types::Seq::<i32>::empty().push(10i32).push(20i32).push(30i32)
                    .map(trust_vc_types::SpecFn::new(|(i, a): (usize, i32)| 2i32 * (i as i32) + a))
                    .index(2usize) == 34i32
            );
        }
    "#;
    assert_verified(code, "test");
}

/// The index cast in isolation: `[10,20,30].map(|i,a| i as i32).index(2) == 2`.
#[test]
fn map_index_cast_only_verifies() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            trust_vc::assert!(
                trust_vc_types::Seq::<i32>::empty().push(10i32).push(20i32).push(30i32)
                    .map(trust_vc_types::SpecFn::new(|(i, a): (usize, i32)| i as i32))
                    .index(2usize) == 2i32
            );
        }
    "#;
    assert_verified(code, "test");
}

/// SOUNDNESS: a wrong value (`34` claimed as `99`) must refute.
#[test]
fn map_index_cast_wrong_value_refutes() {
    let code = r#"
        #[trust_vc::ensures(true)]
        fn test() {
            trust_vc::assert!(
                trust_vc_types::Seq::<i32>::empty().push(10i32).push(20i32).push(30i32)
                    .map(trust_vc_types::SpecFn::new(|(i, a): (usize, i32)| 2i32 * (i as i32) + a))
                    .index(2usize) == 99i32
            );
        }
    "#;
    assert_not_verified(code, "test");
}
