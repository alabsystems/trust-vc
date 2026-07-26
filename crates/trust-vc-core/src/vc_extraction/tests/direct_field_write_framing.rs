// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness + parity regressions for DIRECT field / index writes on owned and
//! `&mut` parameter structs (cluster P0-A).
//!
//! Before this fix, a direct field assignment `s.x = v` (named, tuple, or nested)
//! to an owned local or a struct parameter fell through every `assign_expr`
//! handler AND the fail-closed net (which fired only for erased-mut-ref aliases or
//! `Expr::Index` LHS), so the write VANISHED: the field stayed frozen at its
//! constructed/entry value and a post-write claim of the OLD value falsely
//! `Verified`. The fix models a direct field write as a functional struct update
//! (`assign_direct_field_expr` / `build_nested_field_update`), so a false
//! post-state claim counterexamples and a true one verifies. For a non-scalar
//! `&mut` parameter mutated by a direct field/index write (or whose reference is
//! reborrowed), a postcondition reading it FAILS CLOSED (the two-state final value
//! is not threaded into the entry snapshot the postcondition reads).

use super::*;
use crate::encoder::VerifyResult;

fn verdict(code: &str, func: &str) -> VerifyResult {
    let file = parse_file(code).expect("fixture should parse");
    let item =
        find_function(&file, func).unwrap_or_else(|| panic!("fixture should define fn {func}"));
    extract_verification_conditions_with_file_context(&file, item)
        .map(|vc| vc.verify())
        .unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        })
}

fn assert_verified(code: &str, func: &str) {
    assert_eq!(
        verdict(code, func),
        VerifyResult::Verified,
        "fn {func} should verify"
    );
}

fn assert_counterexample(code: &str, func: &str) {
    assert!(
        matches!(verdict(code, func), VerifyResult::Counterexample { .. }),
        "fn {func} should counterexample, got {:?}",
        verdict(code, func)
    );
}

fn assert_not_verified(code: &str, func: &str) {
    let v = verdict(code, func);
    assert_ne!(
        v,
        VerifyResult::Verified,
        "fn {func} must NOT verify, got {v:?}"
    );
}

// ===========================================================================
// SOUNDNESS — a stale post-write field claim counterexamples (was Verified).
// ===========================================================================

#[test]
fn owned_local_named_field_write_stale_claim_is_counterexample() {
    assert_counterexample(
        r#"
        struct S { x: u64, y: u64 }
        fn f() { let mut s = S { x: 5u64, y: 0u64 }; s.x = 99u64; trust_vc::assert!(s.x == 5u64); }
        "#,
        "f",
    );
}

#[test]
fn mut_ref_named_field_write_stale_claim_is_counterexample() {
    assert_counterexample(
        r#"
        struct S { x: u64, y: u64 }
        #[trust_vc::requires(s.x == 5u64)]
        fn f(s: &mut S) { s.x = 99u64; trust_vc::assert!(s.x == 5u64); }
        "#,
        "f",
    );
}

#[test]
fn owned_param_named_field_write_stale_claim_is_counterexample() {
    assert_counterexample(
        r#"
        struct S { x: u64, y: u64 }
        #[trust_vc::requires(s.x == 5u64)]
        fn f(mut s: S) { s.x = 99u64; trust_vc::assert!(s.x == 5u64); }
        "#,
        "f",
    );
}

#[test]
fn nested_field_write_stale_claim_is_counterexample() {
    assert_counterexample(
        r#"
        struct S { x: u64 }
        struct Nest { inner: S }
        #[trust_vc::requires(s.inner.x == 5u64)]
        fn f(s: &mut Nest) { s.inner.x = 99u64; trust_vc::assert!(s.inner.x == 5u64); }
        "#,
        "f",
    );
}

#[test]
fn tuple_struct_field_write_stale_claim_is_counterexample() {
    assert_counterexample(
        r#"
        struct Pair(u64, u64);
        #[trust_vc::requires(p.0 == 5u64)]
        fn f(p: &mut Pair) { p.0 = 99u64; trust_vc::assert!(p.0 == 5u64); }
        "#,
        "f",
    );
}

// ===========================================================================
// NO OVER-REJECTION — the TRUE post-write field value verifies (precise model).
// ===========================================================================

#[test]
fn owned_local_named_field_write_true_claim_verifies() {
    assert_verified(
        r#"
        struct S { x: u64, y: u64 }
        fn f() { let mut s = S { x: 5u64, y: 0u64 }; s.x = 99u64; trust_vc::assert!(s.x == 99u64); }
        "#,
        "f",
    );
}

#[test]
fn mut_ref_named_field_write_true_claim_verifies() {
    assert_verified(
        r#"
        struct S { x: u64, y: u64 }
        #[trust_vc::requires(s.x == 5u64)]
        fn f(s: &mut S) { s.x = 99u64; trust_vc::assert!(s.x == 99u64); }
        "#,
        "f",
    );
}

#[test]
fn named_field_write_leaves_sibling_field_unchanged() {
    // The functional update must preserve the OTHER field.
    assert_verified(
        r#"
        struct S { x: u64, y: u64 }
        fn f() { let mut s = S { x: 5u64, y: 7u64 }; s.x = 99u64; trust_vc::assert!(s.y == 7u64); }
        "#,
        "f",
    );
}

#[test]
fn nested_field_write_true_claim_verifies() {
    assert_verified(
        r#"
        struct S { x: u64 }
        struct Nest { inner: S }
        #[trust_vc::requires(s.inner.x == 5u64)]
        fn f(s: &mut Nest) { s.inner.x = 99u64; trust_vc::assert!(s.inner.x == 99u64); }
        "#,
        "f",
    );
}

#[test]
fn tuple_struct_field_write_true_claim_verifies() {
    assert_verified(
        r#"
        struct Pair(u64, u64);
        #[trust_vc::requires(p.0 == 5u64)]
        fn f(p: &mut Pair) { p.0 = 99u64; trust_vc::assert!(p.0 == 99u64); }
        "#,
        "f",
    );
}

// ===========================================================================
// SOUNDNESS — a postcondition over a `&mut` param mutated by a direct
// field/index write or a reborrow FAILS CLOSED (was a false Verified).
// ===========================================================================

#[test]
fn mut_ref_struct_field_write_postcondition_fails_closed() {
    assert_not_verified(
        r#"
        struct S { x: u64 }
        #[trust_vc::requires(s.x == 5u64)]
        #[trust_vc::ensures(s.x == 5u64)]
        fn f(s: &mut S) { s.x = 99u64; }
        "#,
        "f",
    );
}

#[test]
fn mut_ref_vec_index_write_postcondition_fails_closed() {
    assert_not_verified(
        r#"
        #[trust_vc::requires(v.len() == 5usize)]
        #[trust_vc::requires(v.index(0usize) == 1u64)]
        #[trust_vc::ensures(v.index(0usize) == 1u64)]
        fn f(v: &mut Vec<u64>) { v[0usize] = 99u64; }
        "#,
        "f",
    );
}

#[test]
fn mut_ref_array_index_write_postcondition_fails_closed() {
    assert_not_verified(
        r#"
        #[trust_vc::requires(ar.index(0usize) == 1u64)]
        #[trust_vc::ensures(ar.index(0usize) == 1u64)]
        fn f(ar: &mut [u64; 3]) { ar[0usize] = 99u64; }
        "#,
        "f",
    );
}

#[test]
fn mut_ref_vec_reborrow_push_postcondition_fails_closed() {
    assert_not_verified(
        r#"
        #[trust_vc::requires(v.len() == 5usize)]
        #[trust_vc::ensures(v.len() == 5usize)]
        fn f(v: &mut Vec<u64>) { let r = &mut *v; r.push(1u64); }
        "#,
        "f",
    );
}

// ── CONDITIONAL-BRANCH / match-arm field writes (round-2 audit P0-A residual) ──
// A field write inside an `if`/`match` branch was DROPPED at the join: the struct
// reverted to its `&mut`/owned-param entry value, so a post-join `assert!` of the
// entry value falsely `Verified`. The join now havocs a struct assigned on only
// some branches (or to differing values), so the false claim no longer verifies.

#[test]
fn conditional_both_branch_field_write_fails_closed() {
    assert_not_verified(
        r#"
        struct S { x: u64, y: u64 }
        #[trust_vc::requires(s.x == 5u64)]
        fn f(s: &mut S, b: bool) {
            if b { s.x = 99u64; } else { s.x = 100u64; }
            trust_vc::assert!(s.x == 5u64);
        }
        "#,
        "f",
    );
}

#[test]
fn conditional_single_branch_field_write_fails_closed() {
    assert_not_verified(
        r#"
        struct S { x: u64, y: u64 }
        #[trust_vc::requires(s.x == 5u64)]
        fn f(s: &mut S, b: bool) {
            if b { s.x = 99u64; }
            trust_vc::assert!(s.x == 5u64);
        }
        "#,
        "f",
    );
}

#[test]
fn match_arm_field_write_fails_closed() {
    assert_not_verified(
        r#"
        struct S { x: u64, y: u64 }
        #[trust_vc::requires(s.x == 5u64)]
        fn f(s: &mut S, sel: u64) {
            match sel { 0u64 => { s.x = 99u64; } _ => { s.x = 100u64; } }
            trust_vc::assert!(s.x == 5u64);
        }
        "#,
        "f",
    );
}

#[test]
fn conditional_compound_field_write_fails_closed() {
    assert_not_verified(
        r#"
        struct S { x: u64, y: u64 }
        #[trust_vc::requires(s.x == 5u64)]
        fn f(s: &mut S, b: bool) {
            if b { s.x += 1u64; }
            trust_vc::assert!(s.x == 5u64);
        }
        "#,
        "f",
    );
}

#[test]
fn both_branches_same_field_value_still_verifies() {
    // NO over-rejection: when both branches write the SAME value, the common-value
    // merge keeps it precise, so the true post-join claim still verifies.
    assert_verified(
        r#"
        struct S { x: u64, y: u64 }
        #[trust_vc::requires(s.x == 5u64)]
        fn f(s: &mut S, b: bool) {
            if b { s.x = 7u64; } else { s.x = 7u64; }
            trust_vc::assert!(s.x == 7u64);
        }
        "#,
        "f",
    );
}
