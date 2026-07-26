// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Faithful 1:1 executable TrustVc port of upstream
// rust_verify_test/tests/choose.rs.
//
// Every one of the 17 upstream harness cases is reproduced here (with the
// two multi-subproof cases test1 and test1_tuple split into their upstream
// subproofs), for a total of 20 executable TrustVc functions:
//   * 7 spec fns (f, f2, cnatf, cintf, cnatf2, cintf2, less_than) mirror the
//     upstream `spec fn` declarations,
//   * `trust_vc::choose!(|x: T| ...)` and source-style `choose|x: T| ...` cover
//     single- and multi-binder witness extraction,
//   * `choose_tuple::<(..), _>(|..| ..)` covers the tuple-projection refinement
//     cases,
//   * casts (`n as int`), tuple destructuring, and nat/int binders mirror the
//     upstream refinement shapes,
//   * the two malformed inputs (`choose(|i, j| ..)` parenthesized closure and
//     the wrong-type `choose_tuple` ascription) reproduce the upstream compile
//     errors verbatim via the general frontend diagnostics.
//
// CHOOSE_RS_EXPECTED_CASES maps each port fn to its upstream harness case id and
// the verdict TrustVc must reproduce. The manifest row keeps the identical
// mapping (see evals/verus/verus-tests.json) and the executable regression guard
// at crates/trust-vc/tests/choose_rs_trust_vc_regressions.rs cross-checks all
// three against each other.

use trust_vc_types::{int, nat};

pub const CHOOSE_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("test1_choose", "test1", "verified", 3),
    ("test1_choose_inference", "test1", "verified", 3),
    ("test1_choose_eq", "test1", "verified", 2),
    ("test1_fails1", "test1_fails1", "counterexample", 2),
    ("test1_fails2", "test1_fails2", "counterexample", 3),
    ("test1_fails3", "test1_fails3", "counterexample", 2),
    ("test_refine", "test_refine", "verified", 3),
    ("test_refine_fail1", "test_refine_fail1", "counterexample", 3),
    ("test_refine2", "test_refine2", "verified", 3),
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

pub fn choose_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    CHOOSE_RS_EXPECTED_CASES
}

#[trust_vc::spec]
fn f(i: int) -> bool {
    5 <= i
}

#[trust_vc::spec]
fn f2(i: int, j: int) -> bool {
    i <= j
}

#[trust_vc::spec]
fn cnatf(n: nat) -> bool {
    true
}

#[trust_vc::spec]
fn cintf(n: int) -> bool {
    true
}

#[trust_vc::spec]
fn cnatf2(m: nat, n: nat) -> bool {
    true
}

#[trust_vc::spec]
fn cintf2(m: int, n: int) -> bool {
    true
}

#[trust_vc::spec]
fn less_than(x: int, y: int) -> bool {
    x < y
}

// ---- test1 (3 subproofs) => Ok ----
#[trust_vc::ensures(true)]
fn test1_choose() {
    let i: int = trust_vc::choose!(|i: int| f(i));
    trust_vc::assert!(f(7));
    trust_vc::assert!(5 <= i);
}
#[trust_vc::ensures(true)]
fn test1_choose_inference() {
    let i: int = trust_vc::choose!(|i| f(i));
    trust_vc::assert!(f(7));
    trust_vc::assert!(5 <= i);
}
#[trust_vc::ensures(true)]
fn test1_choose_eq() {
    let i1: int = trust_vc::choose!(|i: int| f(i) && (1 + 1 == 2));
    let i2: int = trust_vc::choose!(|i: int| f(i) && (2 + 2 == 4));
    trust_vc::assert!(i1 == i2);
}

// ---- test1_fails1/2/3 => CE ----
#[trust_vc::ensures(true)]
fn test1_fails1() {
    let i: int = trust_vc::choose!(|i: int| f(i));
    trust_vc::assert!(5 <= i); // FAILS
}
#[trust_vc::ensures(true)]
fn test1_fails2() {
    let i: int = trust_vc::choose!(|i: int| f(i));
    trust_vc::assert!(f(7));
    trust_vc::assert!(i == 7); // FAILS
}
#[trust_vc::ensures(true)]
fn test1_fails3() {
    let i1: int = trust_vc::choose!(|i: int| f(i) && (2 + 2 == 4));
    let i2: int = trust_vc::choose!(|i: int| (2 + 2 == 4) && f(i));
    trust_vc::assert!(i1 == i2); // FAILS (extensional eq)
}

// ---- test_refine / test_refine_fail1 / test_refine2 ----
#[trust_vc::ensures(true)]
fn test_refine() {
    trust_vc::assert!((choose|n: nat| cnatf(n)) >= 0);
    trust_vc::assert!((choose|n: nat| cintf(n as int) && n < 0) >= 0);
}
#[trust_vc::ensures(true)]
fn test_refine_fail1() {
    trust_vc::assert!(cintf(-10));
    trust_vc::assert!((choose|n: nat| cintf(n as int) && n < 0) < 0); // FAILS
}
#[trust_vc::ensures(true)]
fn test_refine2() {
    trust_vc::assert!(cnatf(10));
    trust_vc::assert!((choose|n: nat| cnatf(n) && n >= 10) >= 10);
}

// ---- test1_choose_with_closure_illegal => Err (parens) ----
#[trust_vc::ensures(true)]
fn test1_choose_with_closure_illegal() {
    let (i, j): (int, int) = choose(|i: int, j: int| f2(i, j));
    trust_vc::assert!(f2(7, 8));
    trust_vc::assert!(i <= j);
}

// ---- test1_tuple (2 subproofs) => Ok ----
#[trust_vc::ensures(true)]
fn test1_tuple_choose() {
    let (i, j): (int, int) = trust_vc::choose!(|i: int, j: int| f2(i, j));
    trust_vc::assert!(f2(7, 8));
    trust_vc::assert!(i <= j);
}
#[trust_vc::ensures(true)]
fn test1_tuple_choose_eq() {
    let (i1, j1): (int, int) = trust_vc::choose!(|i: int, j: int| f2(i, j) && (1 + 1 == 2));
    let (i2, j2): (int, int) = trust_vc::choose!(|i: int, j: int| f2(i, j) && (2 + 2 == 4));
    trust_vc::assert!(i1 == i2);
    trust_vc::assert!(j1 == j2);
}

// ---- tuple fails => CE ----
#[trust_vc::ensures(true)]
fn test1_fails1_tuple() {
    let (i, j): (int, int) = trust_vc::choose!(|i: int, j: int| f2(i, j));
    trust_vc::assert!(i <= j); // FAILS
}
#[trust_vc::ensures(true)]
fn test1_fails2_tuple() {
    let (i, j): (int, int) = trust_vc::choose!(|i: int, j: int| f2(i, j));
    trust_vc::assert!(f2(7, 8));
    trust_vc::assert!(i == 7); // FAILS
}
#[trust_vc::ensures(true)]
fn test1_fails3_tuple() {
    let (i1, j1): (int, int) = trust_vc::choose!(|i: int, j: int| f2(i, j) && (2 + 2 == 4));
    let (i2, j2): (int, int) = trust_vc::choose!(|i: int, j: int| (2 + 2 == 4) && f2(i, j));
    trust_vc::assert!(i1 == i2); // FAILS
}

// ---- test_refine_tuple / fail1_tuple / refine2_tuple ----
#[trust_vc::ensures(true)]
fn test_refine_tuple() {
    trust_vc::assert!(choose_tuple::<(nat, nat), _>(|m: nat, n: nat| cnatf2(m, n)).0 >= 0);
    trust_vc::assert!(choose_tuple::<(nat, nat), _>(|m: nat, n: nat| cintf2(m as int, n as int) && m < 0 && n < 0).0 >= 0);
}
#[trust_vc::ensures(true)]
fn test_refine_fail1_tuple() {
    trust_vc::assert!(cintf2(-10, -10));
    trust_vc::assert!(choose_tuple::<(nat, nat), _>(|m: nat, n: nat| cintf2(m as int, n as int) && m < 0 && n < 0).0 < 0); // FAILS
}
#[trust_vc::ensures(true)]
fn test_refine2_tuple() {
    trust_vc::assert!(cnatf2(10, 10));
    trust_vc::assert!(choose_tuple::<(nat, nat), _>(|m: nat, n: nat| cnatf2(m, n) && m >= 10 && n >= 10).0 >= 10);
}

// ---- test1_choose_tuple_wrong_type => Err ----
#[trust_vc::ensures(true)]
fn test1_choose_tuple_wrong_type() {
    let (i, j): (int, nat) = choose_tuple(|i: int, j: int| f2(i, j));
}

// ---- test1_choose_tuple_no_ascription_regression_1183 => Ok ----
#[trust_vc::ensures(true)]
fn test1_choose_tuple_no_ascription_regression_1183() {
    trust_vc::assert!(less_than(3, 7));
    let (x, y) = trust_vc::choose!(|i: int, j: int| less_than(i, j));
    trust_vc::assert!(x < y);
}
