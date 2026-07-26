// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Faithful 1:1 TrustVc port of upstream
// `source/rust_verify_test/tests/nonlinear.rs` (Verus pin
// a40d57c73650cd3648b09386bfdb96ab5c270626). One TrustVc fn per non-ignored
// upstream case (named after the upstream case id; `test_new_vars` contains
// two upstream fns and is split into `test_new_vars` + `test_new_vars_loop`,
// both mapped to upstream `test_new_vars`), reproducing every case on the
// upstream-shaped surface with the matching verifier verdict:
//
//   upstream case                          upstream outcome            TrustVc verdict
//   -------------------------------------  --------------------------  ---------------
//   test1                                  Ok(())                      verified
//   test2                                  Ok(())                      verified
//   test3                                  Ok(())                      verified
//   test4                                  Ok(())                      verified
//   test1_fails                            Err / assert_one_fails      counterexample
//   test2_fails                            Err / assert_one_fails      counterexample
//   test5                                  Ok(())                      verified
//   test6                                  Ok(())                      verified
//   test_requires                          Err / assert_one_fails      counterexample
//   test7                                  Ok(())                      verified
//   test3_fails                            Err / assert_one_fails      counterexample
//   test4_fails                            Err / assert_one_fails      counterexample
//   test_assert_nonlinear_by_in_nonlinear  Err / assert_vir_error_msg  error
//   test_negative                          Err / assert_one_fails      counterexample
//   test_unexpected_vars                   Err / assert_vir_error_msg  error
//   test_complex_vars                      Ok(())                      verified
//   test_requires_no_block                 Ok(())                      verified
//   test_new_vars                          Ok(())                      verified
//   nlarith1                               #[ignore] (Z3 too slow)     (not ported)
//
// Surface notes (TrustVc spellings of the Verus constructs):
//   * `proof fn f(..) requires .. ensures ..` is written as attribute
//     contracts (`#[trust_vc::requires(..)]`, `#[trust_vc::ensures(..)]`).
//   * `#[verifier(nonlinear)]` is `#[trust_vc::verifier(nonlinear)]`.
//   * `assert(G) by(nonlinear_arith) requires R1, R2 { asserts.. }` is
//     `trust_vc::assert_by_nonlinear!(G; requires R1, R2; { asserts.. })`:
//     each body assert is checked as its own scoped query under the same
//     requires and its fact joins the goal query's hypotheses; an upstream
//     body containing a `let` (test_new_vars) is ported by hoisting the
//     let-free equivalent as its own by-assert with the same scoped requires
//     (identical inner-query context), so every upstream body obligation is
//     still checked.
//   * Verus builtins `add`/`mul` are the same-named TrustVc truncating
//     builtins for fixed-width operands (exact math over int/nat).

#![allow(dead_code, unused_variables)]

use trust_vc_types::{int, nat};

pub type NonlinearRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type NonlinearRsErrorPatterns = (&'static str, &'static [&'static str]);

pub const NONLINEAR_RS_EXPECTED_CASES: &[NonlinearRsExpectedCase] = &[
    ("test1", "test1", "verified", 1),
    ("test2", "test2", "verified", 1),
    ("test3", "test3", "verified", 1),
    ("test4", "test4", "verified", 1),
    ("test1_fails", "test1_fails", "counterexample", 1),
    ("test2_fails", "test2_fails", "counterexample", 1),
    ("test5", "test5", "verified", 1),
    ("test6", "test6", "verified", 1),
    ("test_requires", "test_requires", "counterexample", 1),
    ("test7", "test7", "verified", 1),
    ("test3_fails", "test3_fails", "counterexample", 1),
    ("test4_fails", "test4_fails", "counterexample", 1),
    (
        "test_assert_nonlinear_by_in_nonlinear",
        "test_assert_nonlinear_by_in_nonlinear",
        "error",
        0,
    ),
    ("test_negative", "test_negative", "counterexample", 1),
    ("test_unexpected_vars", "test_unexpected_vars", "error", 0),
    ("test_complex_vars", "test_complex_vars", "verified", 1),
    ("test_requires_no_block", "test_requires_no_block", "verified", 1),
    ("test_new_vars", "test_new_vars", "verified", 1),
    ("test_new_vars_loop", "test_new_vars", "verified", 1),
];

pub const NONLINEAR_RS_ERROR_PATTERNS: &[NonlinearRsErrorPatterns] = &[
    (
        "test_assert_nonlinear_by_in_nonlinear",
        &["assert_by_query not allowed in #[verifier::nonlinear] functions"],
    ),
    (
        "test_unexpected_vars",
        &["not mentioned in requires/ensures"],
    ),
];

pub fn nonlinear_rs_expected_cases() -> &'static [NonlinearRsExpectedCase] {
    NONLINEAR_RS_EXPECTED_CASES
}

pub fn nonlinear_rs_error_patterns() -> &'static [NonlinearRsErrorPatterns] {
    NONLINEAR_RS_ERROR_PATTERNS
}

// upstream `test1` => Ok(()): #[verifier(nonlinear)] proof fn
// lemma_mul_upper_bound. Symbolic unbounded-int product upper bound.
#[trust_vc::verifier(nonlinear)]
#[trust_vc::requires(x <= x_bound)]
#[trust_vc::requires(y <= y_bound)]
#[trust_vc::requires(0 <= x)]
#[trust_vc::requires(0 <= y)]
#[trust_vc::ensures(x * y <= x_bound * y_bound)]
fn test1(x: int, x_bound: int, y: int, y_bound: int) {}

// upstream `test2` => Ok(()): lemma_mul_stay_positive. Product sign.
#[trust_vc::verifier(nonlinear)]
#[trust_vc::requires(0 <= x)]
#[trust_vc::requires(0 <= y)]
#[trust_vc::ensures(0 <= x * y)]
fn test2(x: int, y: int) {}

// upstream `test3` => Ok(()): lemma_inequality_after_mul. Multiplication
// monotonicity.
#[trust_vc::verifier(nonlinear)]
#[trust_vc::requires(x <= y)]
#[trust_vc::requires(0 <= z)]
#[trust_vc::ensures(x * z <= y * z)]
fn test3(x: int, y: int, z: int) {}

// upstream `test4` => Ok(()): lemma_div_pos_is_pos. Euclidean quotient sign
// with a SYMBOLIC divisor.
#[trust_vc::verifier(nonlinear)]
#[trust_vc::requires(0 <= x)]
#[trust_vc::requires(0 < d)]
#[trust_vc::ensures(0 <= x / d)]
fn test4(x: int, d: int) {}

// upstream `test1_fails` => Err(e) => assert_one_fails(e): wrong_lemma_1.
// Strict monotonicity is FALSE (z == 0 or x == y refutes).
#[trust_vc::verifier(nonlinear)]
#[trust_vc::requires(x <= y)]
#[trust_vc::requires(0 <= z)]
#[trust_vc::ensures(x * z < y * z)] // FAILS
fn test1_fails(x: int, y: int, z: int) {}

// upstream `test2_fails` => Err(e) => assert_one_fails(e): wrong_lemma_2.
#[trust_vc::verifier(nonlinear)]
#[trust_vc::requires(x > y)]
#[trust_vc::requires(3 <= z)]
#[trust_vc::ensures(y * z > x)] // FAILS
fn test2_fails(x: int, y: int, z: int) {}

// upstream `test5` => Ok(()): bound-checked truncating-mul equivalence, twice,
// with the upstream proof-block bodies verbatim.
#[trust_vc::requires(x <= 0xffff)]
#[trust_vc::requires(y <= 0xffff)]
#[trust_vc::requires(z <= 0xffff)]
#[trust_vc::ensures(true)]
fn test5(x: u32, y: u32, z: u32) {
    trust_vc::assert_by_nonlinear!(
        x * z == mul(x, z);
        requires x <= 0xffff, z <= 0xffff;
        {
            trust_vc::assert!(0 <= x * z);
            trust_vc::assert!(x * z <= 0xffff * 0xffff);
        }
    );
    trust_vc::assert!(x * z == mul(x, z));

    trust_vc::assert_by_nonlinear!(
        y * z == mul(y, z);
        requires y <= 0xffff, z <= 0xffff;
        {
            trust_vc::assert!(0 <= y * z);
            trust_vc::assert!(y * z <= 0xffff * 0xffff);
        }
    );
    trust_vc::assert!(y * z == mul(y, z));
}

// upstream `test6` => Ok(()): truncating add/mul factorization (empty upstream
// proof block, kept verbatim) + unscoped truncating-mul commutativity.
#[trust_vc::requires(x < 0xfff)]
#[trust_vc::ensures(true)]
fn test6(x: u32, y: u32, z: u32) {
    trust_vc::assert_by_nonlinear!(
        add(mul(x, x), x) == mul(x, add(x, 1));
        requires x < 0xfff;
        {}
    );
    trust_vc::assert!(add(mul(x, x), x) == mul(x, add(x, 1)));

    trust_vc::assert_by_nonlinear!(mul(x, y) == mul(y, x));
    trust_vc::assert!(mul(x, y) == mul(y, x));
}

// upstream `test_requires` => Err(e) => assert_one_fails(e): the scoped
// `requires x < 0xfff` is not provable from the (empty) enclosing context.
#[trust_vc::ensures(true)]
fn test_requires(x: nat, y: nat, z: nat) {
    trust_vc::assert_by_nonlinear!(x * x + x == x * (x + 1); requires x < 0xfff); // FAILS
    trust_vc::assert!(x * x + x == x * (x + 1));
}

// upstream `test7` => Ok(()): symbolic int distributivity (upstream inner fn
// is named test6).
#[trust_vc::ensures(true)]
fn test7(x: int, y: int, z: int) {
    trust_vc::assert_by_nonlinear!((x + y) * z == x * z + y * z);
    trust_vc::assert!((x + y) * z == x * z + y * z);

    trust_vc::assert_by_nonlinear!((x - y) * z == x * z - y * z);
    trust_vc::assert!((x - y) * z == x * z - y * z);
}

// upstream `test3_fails` => Err(e) => assert_one_fails(e): unrelated products.
#[trust_vc::ensures(true)]
fn test3_fails(x: int, y: int, z: int) {
    trust_vc::assert_by_nonlinear!(x * y == y * z); // FAILS
}

// upstream `test4_fails` => Err(e) => assert_one_fails(e): the UNBOUNDED exact
// product does not equal the truncating builtin without range requires.
#[trust_vc::ensures(true)]
fn test4_fails(x: u32, y: u32, z: u32) {
    trust_vc::assert_by_nonlinear!(x * z == (mul(x, z) as int)); // FAILS
}

// upstream `test_assert_nonlinear_by_in_nonlinear` => Err(err) =>
// assert_vir_error_msg(err, "assert_by_query not allowed in
// #[verifier::nonlinear] functions").
#[trust_vc::verifier(nonlinear)]
#[trust_vc::requires(x < 0xfff)]
#[trust_vc::ensures(true)]
fn test_assert_nonlinear_by_in_nonlinear(x: u32) {
    trust_vc::assert_by_nonlinear!(x * x + x == x * (x + 1); requires x < 0xfff);
    trust_vc::assert!(x * x + x == x * (x + 1));
}

// upstream `test_negative` => Err(e) => assert_one_fails(e): a passing
// nonlinear by-assert followed by assert(false).
#[trust_vc::ensures(true)]
fn test_negative(x: int, y: int, z: int) {
    trust_vc::assert_by_nonlinear!((x + y) * z == x * z + y * z);
    trust_vc::assert!(false); // FAILS
}

// upstream `test_unexpected_vars` => Err(err) => assert_vir_error_msg(err,
// "not mentioned in requires/ensures"): the by-block proof body mentions `z`,
// which is not part of the scoped query interface (goal + requires).
#[trust_vc::requires(y == 0)]
#[trust_vc::requires(z == 0)]
#[trust_vc::ensures(true)]
fn test_unexpected_vars(x: int, y: int, z: int) {
    trust_vc::assert_by_nonlinear!(
        x + y == x;
        requires y == 0;
        {
            trust_vc::assert!(z == 0);
        }
    );
}

// upstream `test_complex_vars` => Ok(()): tuple-destructured scoped values
// feeding a scoped requires (upstream inner fn is named test6).
#[trust_vc::ensures(true)]
fn test_complex_vars(a1: int, a2: int) {
    let (b1, b2) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
    trust_vc::assert_by_nonlinear!(b1 <= b2; requires b1 <= b2);
}

// upstream `test_requires_no_block` => Ok(()): the same query in the
// no-proof-block form (upstream inner fn is named test6).
#[trust_vc::ensures(true)]
fn test_requires_no_block(a1: int, a2: int) {
    let (b1, b2) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
    trust_vc::assert_by_nonlinear!(b1 <= b2; requires b1 <= b2);
}

// upstream `test_new_vars` => Ok(()) (first upstream fn, proof fn test6):
// block-local lets in the goal and scoped requires; the upstream proof-block
// body (`let y: nat = mul(x as nat, 2); assert(y == 10)`) is hoisted as its
// own by-assert with the same scoped requires.
#[trust_vc::requires(x == 5)]
#[trust_vc::ensures(true)]
fn test_new_vars(x: int) {
    trust_vc::assert_by_nonlinear!(
        mul(x as nat, 2) == 10;
        requires ({ let z: int = 5; x == z })
    );
    trust_vc::assert_by_nonlinear!(
        { let z: int = 2; x * z == 10 };
        requires ({ let z: int = 5; x == z })
    );
    trust_vc::assert!(x * 2 == 10);
}

// upstream `test_new_vars` (second upstream fn, exec fn test7 under
// ["exec_allows_no_decreases_clause"]): a decreases-free loop whose body runs
// a trivially-true nonlinear by-assert with a block-local scoped requires.
#[trust_vc::ensures(true)]
fn test_new_vars_loop(n: u32) {
    loop {
        trust_vc::assert_by_nonlinear!(true; requires ({ let q = n; q <= n }));
        break;
    }
}
