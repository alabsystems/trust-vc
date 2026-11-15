// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Faithful 1:1 executable TrustVc port of the MULTI-BINDER / choose_tuple half
// of upstream rust_verify_test/tests/choose.rs.
//
// WHY THIS FILE EXISTS. Upstream's `test_verify_one_file!` blocks are separate
// compilation units, and the `test1_tuple*` / `test_refine*_tuple` blocks
// re-declare `f`, `cnatf` and `cintf` at arity 2 — not as renames of the 1-ary
// declarations in the single-binder blocks, which live in `choose.rs`. Keeping
// both halves in one Rust file forced the 2-ary helpers to be spelled `f2`,
// `cnatf2`, `cintf2`, and the corpus gate then compared
// `test_refine_fail1_tuple`'s refuted statement against an upstream line that
// says `cintf`, not `cintf2`, and correctly found no correspondence. Splitting
// at upstream's own compilation-unit boundary restores upstream's names without
// touching what any case claims. See `choose.rs`'s header for the full note.
//
// This file reproduces the 10 multi-binder upstream harness cases
// (test1_choose_with_closure_illegal, test1_tuple, test1_fails1_tuple,
// test1_fails2_tuple, test1_fails3_tuple, test_refine_tuple,
// test_refine_fail1_tuple, test_refine2_tuple, test1_choose_tuple_wrong_type,
// test1_choose_tuple_no_ascription_regression_1183), with the multi-subproof
// case `test1_tuple` split into its upstream subproofs, for a total of 11
// executable TrustVc functions:
//   * 4 spec fns (f, cnatf, cintf, less_than) mirror the upstream `spec fn`
//     declarations at upstream's own names and arities,
//   * `choose_tuple::<(..), _>(|..| ..)` covers the tuple-projection refinement
//     cases and `trust_vc::choose!(|i: T, j: T| ..)` the multi-binder witness,
//   * tuple destructuring, casts (`m as int`) and nat/int binders mirror the
//     upstream refinement shapes,
//   * the two malformed inputs (`choose(|i, j| ..)` parenthesized closure and
//     the wrong-type `choose_tuple` ascription) reproduce the upstream compile
//     errors verbatim via the general frontend diagnostics.
//
// CHOOSE_TUPLE_RS_EXPECTED_CASES maps each port fn to its upstream harness case
// id and the verdict TrustVc must reproduce. The manifest row keeps the
// identical mapping (see evals/verus/verus-tests.json) and the executable
// regression guard at crates/trust-vc/tests/choose_rs_trust_vc_regressions.rs
// cross-checks all three against each other.

use trust_vc_types::{int, nat};

pub const CHOOSE_TUPLE_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "test1_choose_with_closure_illegal",
        "test1_choose_with_closure_illegal",
        "error",
        0,
    ),
    ("test1_tuple_choose", "test1_tuple", "verified", 3),
    ("test1_tuple_choose_eq", "test1_tuple", "verified", 3),
    ("test1_fails1_tuple", "test1_fails1_tuple", "counterexample", 2),
    ("test1_fails2_tuple", "test1_fails2_tuple", "counterexample", 3),
    ("test1_fails3_tuple", "test1_fails3_tuple", "counterexample", 2),
    ("test_refine_tuple", "test_refine_tuple", "verified", 3),
    (
        "test_refine_fail1_tuple",
        "test_refine_fail1_tuple",
        "counterexample",
        3,
    ),
    ("test_refine2_tuple", "test_refine2_tuple", "verified", 3),
    (
        "test1_choose_tuple_wrong_type",
        "test1_choose_tuple_wrong_type",
        "error",
        0,
    ),
    (
        "test1_choose_tuple_no_ascription_regression_1183",
        "test1_choose_tuple_no_ascription_regression_1183",
        "verified",
        3,
    ),
];

pub fn choose_tuple_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    CHOOSE_TUPLE_RS_EXPECTED_CASES
}

#[trust_vc::spec]
fn f(i: int, j: int) -> bool {
    i <= j
}

#[trust_vc::spec]
fn cnatf(m: nat, n: nat) -> bool {
    true
}

#[trust_vc::spec]
fn cintf(m: int, n: int) -> bool {
    true
}

#[trust_vc::spec]
fn less_than(x: int, y: int) -> bool {
    x < y
}

// ---- test1_choose_with_closure_illegal => Err (parens) ----
#[trust_vc::ensures(true)]
fn test1_choose_with_closure_illegal() {
    let (i, j): (int, int) = choose(|i: int, j: int| f(i, j));
    trust_vc::assert!(f(7, 8));
    trust_vc::assert!(i <= j);
}

// ---- test1_tuple (2 subproofs) => Ok ----
#[trust_vc::ensures(true)]
fn test1_tuple_choose() {
    let (i, j): (int, int) = trust_vc::choose!(|i: int, j: int| f(i, j));
    trust_vc::assert!(f(7, 8));
    trust_vc::assert!(i <= j);
}
#[trust_vc::ensures(true)]
fn test1_tuple_choose_eq() {
    let (i1, j1): (int, int) = trust_vc::choose!(|i: int, j: int| f(i, j) && (1 + 1 == 2));
    let (i2, j2): (int, int) = trust_vc::choose!(|i: int, j: int| f(i, j) && (2 + 2 == 4));
    trust_vc::assert!(i1 == i2);
    trust_vc::assert!(j1 == j2);
}

// ---- tuple fails => CE ----
#[trust_vc::ensures(true)]
fn test1_fails1_tuple() {
    let (i, j): (int, int) = trust_vc::choose!(|i: int, j: int| f(i, j));
    trust_vc::assert!(i <= j); // FAILS
}
#[trust_vc::ensures(true)]
fn test1_fails2_tuple() {
    let (i, j): (int, int) = trust_vc::choose!(|i: int, j: int| f(i, j));
    trust_vc::assert!(f(7, 8));
    trust_vc::assert!(i == 7); // FAILS
}
#[trust_vc::ensures(true)]
fn test1_fails3_tuple() {
    let (i1, j1): (int, int) = trust_vc::choose!(|i: int, j: int| f(i, j) && (2 + 2 == 4));
    let (i2, j2): (int, int) = trust_vc::choose!(|i: int, j: int| (2 + 2 == 4) && f(i, j));
    trust_vc::assert!(i1 == i2); // FAILS
}

// ---- test_refine_tuple / fail1_tuple / refine2_tuple ----
#[trust_vc::ensures(true)]
fn test_refine_tuple() {
    trust_vc::assert!(choose_tuple::<(nat, nat), _>(|m: nat, n: nat| cnatf(m, n)).0 >= 0);
    trust_vc::assert!(choose_tuple::<(nat, nat), _>(|m: nat, n: nat| cintf(m as int, n as int) && m < 0 && n < 0).0 >= 0);
}
#[trust_vc::ensures(true)]
fn test_refine_fail1_tuple() {
    trust_vc::assert!(cintf(-10, -10));
    trust_vc::assert!(choose_tuple::<(nat, nat), _>(|m: nat, n: nat| cintf(m as int, n as int) && m < 0 && n < 0).0 < 0); // FAILS
}
#[trust_vc::ensures(true)]
fn test_refine2_tuple() {
    trust_vc::assert!(cnatf(10, 10));
    trust_vc::assert!(choose_tuple::<(nat, nat), _>(|m: nat, n: nat| cnatf(m, n) && m >= 10 && n >= 10).0 >= 10);
}

// ---- test1_choose_tuple_wrong_type => Err ----
#[trust_vc::ensures(true)]
fn test1_choose_tuple_wrong_type() {
    let (i, j): (int, nat) = choose_tuple(|i: int, j: int| f(i, j));
}

// ---- test1_choose_tuple_no_ascription_regression_1183 => Ok ----
#[trust_vc::ensures(true)]
fn test1_choose_tuple_no_ascription_regression_1183() {
    trust_vc::assert!(less_than(3, 7));
    let (x, y) = trust_vc::choose!(|i: int, j: int| less_than(i, j));
    trust_vc::assert!(x < y);
}
