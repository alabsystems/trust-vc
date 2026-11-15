// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Faithful 1:1 executable TrustVc port of the SINGLE-BINDER half of upstream
// rust_verify_test/tests/choose.rs.
//
// WHY THE PORT IS TWO FILES. Upstream's file is a sequence of
// `test_verify_one_file!` blocks, and each block is its OWN compilation unit.
// Three helper names are therefore declared more than once upstream at
// DIFFERENT ARITIES: `f` is 1-ary in the `test1*` blocks and 2-ary in the
// `test1_tuple*` blocks, and `cnatf`/`cintf` are 1-ary in the `test_refine*`
// blocks and 2-ary in the `test_refine*_tuple` blocks. They are not renames of
// each other. Flattening every block into one Rust file collided those names,
// and the port resolved the collision by RENAMING the 2-ary ones to `f2`,
// `cnatf2` and `cintf2`.
//
// That rename is a spelling upstream never writes, and the corpus gate compares
// a refuted statement against upstream's own `// FAILS` line: the renamed
// `cintf2` made `test_refine_fail1_tuple` correspond to no upstream statement.
// A module wrapper does not fix it either — the claim canonicalizer strips a
// literal `trust_vc::` prefix and a turbofish and nothing else, so `m::cintf(..)`
// does not reduce to upstream's `cintf(..)`, and a general path-prefix
// reduction would wrongly equate `Seq::empty()` with `Set::empty()`
// (pinned by `path_qualified_call_is_not_the_bare_call` in
// crates/cargo-trust-vc/src/evidence.rs).
//
// The honest repair is to give the port the SAME compilation-unit boundary
// upstream has, so each helper keeps upstream's own name at upstream's own
// arity. The 2-ary half lives in `choose_tuple.rs`; nothing about what any case
// CLAIMS or which obligation FAILS changed.
//
// This file reproduces the 7 single-binder upstream harness cases (test1,
// test1_fails1, test1_fails2, test1_fails3, test_refine, test_refine_fail1,
// test_refine2), with the multi-subproof case `test1` split into its upstream
// subproofs, for a total of 9 executable TrustVc functions:
//   * 3 spec fns (f, cnatf, cintf) mirror the upstream `spec fn` declarations
//     at upstream's own names and arities,
//   * `trust_vc::choose!(|x: T| ...)` and source-style `choose|x: T| ...` cover
//     single-binder witness extraction,
//   * casts (`n as int`) and nat/int binders mirror the upstream refinement
//     shapes.
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
];

pub fn choose_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    CHOOSE_RS_EXPECTED_CASES
}

#[trust_vc::spec]
fn f(i: int) -> bool {
    5 <= i
}

#[trust_vc::spec]
fn cnatf(n: nat) -> bool {
    true
}

#[trust_vc::spec]
fn cintf(n: int) -> bool {
    true
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
