// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! #2777 choose.rs: `choose` extensionality / determinism-key normalization.
//!
//! Two `choose` expressions share a Skolem witness iff their closures share a
//! determinism key. That key folds CLOSED (variable-free) subexpressions to
//! their values while PRESERVING boolean structure, matching Verus's own
//! predicate identity:
//!
//! * `choose|i| f(i) && (1+1==2)` and `choose|i| f(i) && (2+2==4)` both
//!   normalize to `choose|i| f(i) && true`, so their witnesses are equal
//!   (`test_choose_eq` — Verus proves this); and
//! * the REORDERED `choose|i| (2+2==4) && f(i)` normalizes to
//!   `choose|i| true && f(i)` — a DISTINCT key — so its witness is NOT proven
//!   equal (`test1_fails3` stays refuted). trust-vc must not prove more than
//!   Verus: no commuting `&&`, no dropping `&& true`.
//!
//! These guards pin BOTH directions and the adversarial boundary.

use super::*;

fn verify_src(code: &str, func: &str) -> VerifyResult {
    let file = parse_file(code).unwrap();
    let f = find_function(&file, func).unwrap();
    match extract_verification_conditions_with_file_context(&file, f) {
        Ok(vc) => vc.verify(),
        Err(e) => VerifyResult::Error {
            message: e.to_string(),
        },
    }
}

fn verifies(code: &str) -> bool {
    matches!(verify_src(code, "test"), VerifyResult::Verified)
}

/// `test_choose_eq`: same structure, a different closed constant — the witnesses
/// are equal (both closures normalize to `f(i) && true`).
#[test]
fn extensionality_same_structure_different_constant_verifies() {
    let code = r#"
        fn test() {
            let i1: i32 = choose!(|i: i32| i >= 5i32 && 1i32 + 1i32 == 2i32);
            let i2: i32 = choose!(|i: i32| i >= 5i32 && 2i32 + 2i32 == 4i32);
            assert!(i1 == i2);
        }
    "#;
    assert!(verifies(code), "got {:?}", verify_src(code, "test"));
}

/// SOUNDNESS (`test1_fails3`): REORDERED conjuncts must NOT be proven equal —
/// `f(i) && true` and `true && f(i)` are distinct keys (no commuting).
#[test]
fn extensionality_reordered_conjuncts_not_verified() {
    let code = r#"
        fn test() {
            let i1: i32 = choose!(|i: i32| i >= 5i32 && 2i32 + 2i32 == 4i32);
            let i2: i32 = choose!(|i: i32| 2i32 + 2i32 == 4i32 && i >= 5i32);
            assert!(i1 == i2);
        }
    "#;
    assert!(
        !verifies(code),
        "reordered conjuncts must not prove witness equality (would prove more than Verus), got {:?}",
        verify_src(code, "test")
    );
}

/// Identical closures are deterministic (baseline — must keep working after the
/// key normalization).
#[test]
fn extensionality_identical_closures_verify() {
    let code = r#"
        fn test() {
            let i1: i32 = choose!(|i: i32| i >= 5i32);
            let i2: i32 = choose!(|i: i32| i >= 5i32);
            assert!(i1 == i2);
        }
    "#;
    assert!(verifies(code), "got {:?}", verify_src(code, "test"));
}

/// Two DIFFERENT true constants in the same position both fold to `true`, so the
/// witnesses are equal.
#[test]
fn extensionality_two_true_constants_verify() {
    let code = r#"
        fn test() {
            let i1: i32 = choose!(|i: i32| i >= 5i32 && 2i32 + 2i32 == 4i32);
            let i2: i32 = choose!(|i: i32| i >= 5i32 && 3i32 + 3i32 == 6i32);
            assert!(i1 == i2);
        }
    "#;
    assert!(verifies(code), "got {:?}", verify_src(code, "test"));
}

/// SOUNDNESS: a TRUE closed constant vs a FALSE one fold to different values
/// (`&& true` vs `&& false`) — distinct predicates, witnesses not proven equal.
#[test]
fn extensionality_true_vs_false_constant_not_verified() {
    let code = r#"
        fn test() {
            let i1: i32 = choose!(|i: i32| i >= 5i32 && 2i32 + 2i32 == 4i32);
            let i2: i32 = choose!(|i: i32| i >= 5i32 && 2i32 + 2i32 == 5i32);
            assert!(i1 == i2);
        }
    "#;
    assert!(
        !verifies(code),
        "true-vs-false closed constant must not prove witness equality, got {:?}",
        verify_src(code, "test")
    );
}

/// SOUNDNESS sanity: genuinely different predicates (`i >= 5` vs `i >= 6`) are
/// not proven to share a witness.
#[test]
fn extensionality_distinct_predicates_not_verified() {
    let code = r#"
        fn test() {
            let i1: i32 = choose!(|i: i32| i >= 5i32);
            let i2: i32 = choose!(|i: i32| i >= 6i32);
            assert!(i1 == i2);
        }
    "#;
    assert!(
        !verifies(code),
        "distinct predicates must not prove witness equality, got {:?}",
        verify_src(code, "test")
    );
}
