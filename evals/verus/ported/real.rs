// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Faithful 1:1 TrustVc port of upstream
// `source/rust_verify_test/tests/real.rs` (Verus pin
// a40d57c73650cd3648b09386bfdb96ab5c270626). Exactly one TrustVc proof fn per
// upstream proof fn, reproducing every non-ignored upstream case on the
// upstream-shaped surface with the matching verifier verdict:
//
//   upstream case      upstream outcome                 TrustVc verdict
//   ---------------    ------------------------------   ---------------
//   real_basics        Err / assert_one_fails           counterexample
//   real_nonlinear1    Ok(())                            verified
//   real_nonlinear2    Err / assert_one_fails           counterexample
//   archimedean_nat    Ok(())                            verified
//   test_chained       Ok(())                            verified
//   test_reject_mixed  Err / assert_vir_error_msg        error
//
// `real_nonlinear1` is discharged by the `by(nonlinear_arith)` real-certificate
// search; `real_nonlinear2` is the SAME goal with NO hint — ay reports a
// model-less incompleteness non-proof, which (per
// docs/design-unknown-as-failure.md) surfaces as the gate's `counterexample`
// expectation exactly as Verus maps Z3's incompleteness-unknown to a model-less
// `assert_one_fails` failure. `archimedean_nat`'s existential postcondition is
// discharged by straight-line body-assert assumption forwarding (#2778).

#![allow(dead_code, non_camel_case_types)]

pub type RealRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type RealRsFailClosedErrorPatterns = (&'static str, &'static [&'static str]);

pub const REAL_RS_EXPECTED_CASES: &[RealRsExpectedCase] = &[
    ("real_basics", "real_basics", "counterexample", 1),
    ("real_nonlinear1", "real_nonlinear1", "verified", 1),
    ("real_nonlinear2", "real_nonlinear2", "counterexample", 1),
    ("archimedean_nat", "archimedean_nat", "verified", 1),
    ("test_chained", "test_chained", "verified", 1),
    ("test_reject_mixed", "test_reject_mixed", "error", 0),
];

pub const REAL_RS_FAIL_CLOSED_ERROR_PATTERNS: &[RealRsFailClosedErrorPatterns] = &[(
    "test_reject_mixed",
    &["chained inequalities require all elements to have the same type"],
)];

pub fn real_rs_expected_cases() -> &'static [RealRsExpectedCase] {
    REAL_RS_EXPECTED_CASES
}

pub fn real_rs_fail_closed_error_patterns() -> &'static [RealRsFailClosedErrorPatterns] {
    REAL_RS_FAIL_CLOSED_ERROR_PATTERNS
}

// upstream `real_basics` => Err(err) => assert_one_fails(err).
// All ten asserts in one proof fn; every assert holds except the last
// (`x >= 0.0 ==> x / 3.0 > 0.0`, false at x == 0.0), reproducing the single
// upstream failure. Verus `==>` is written as the disjunctive form `!(P) || Q`.
#[trust_vc::ensures(true)]
fn real_basics(i: int, x: real, y: real) {
    trust_vc::assert!(!(x == 0.2real) || x / 2.0 == 0.1real);
    trust_vc::assert!(!(x > 0.0) || x / 3.0 > 0.0);
    trust_vc::assert!(!(x <= 1.0) || x / 3.0 < 1.0);
    let z: real = x + 1.1;
    trust_vc::assert!(z > x);
    let q: real = 5u8 as real;
    trust_vc::assert!(q == 5real);
    trust_vc::assert!((i + 1) as real == i as real + 1.0);
    trust_vc::assert!((2.7real).floor() == 2);
    trust_vc::assert!((-2.7real).floor() == -3);
    trust_vc::assert!(!(x >= 0.0) || x / 3.0 > 0.0); // FAILS
}

// upstream `real_nonlinear1` => Ok(()). The `by(nonlinear_arith)` hint routes
// the goal to the real-certificate pre-pass, which discharges it.
#[trust_vc::ensures(true)]
fn real_nonlinear1(a: real, b: real, q: real) {
    trust_vc::assert_by_nonlinear!(
        !(a >= 0.0 && b >= 0.0 && a * a + b * b == (a * b + 1.0) * q) || q >= 0.0
    );
}

// upstream `real_nonlinear2` => Err(err) => assert_one_fails(err). The SAME goal
// with NO hint: the ordinary solver cannot decide the nonlinear-real fact and
// returns a model-less incompleteness non-proof (no fabricated counterexample),
// surfaced as the gate's `counterexample` expectation — matching Verus, whose
// Z3 incompleteness-unknown becomes a model-less `assert_one_fails`.
#[trust_vc::ensures(true)]
fn real_nonlinear2(a: real, b: real, q: real) {
    trust_vc::assert!(!(a >= 0.0 && b >= 0.0 && a * a + b * b == (a * b + 1.0) * q) || q >= 0.0); // FAILS
}

// upstream `archimedean_nat` => Ok(()). Spec helper mirrors upstream
// `nat_to_real`; the existential postcondition is established by the
// straight-line body assert via assumption forwarding (#2778). Verus
// `exists |n: nat| ...` is written as the call form `exists(|n: nat| ...)`.
#[trust_vc::spec]
fn nat_to_real(n: nat) -> real {
    n as real
}

#[trust_vc::requires(x >= 0)]
#[trust_vc::ensures(exists(|n: nat| nat_to_real(n) >= x))]
fn archimedean_nat(x: real) {
    let a: nat = x.floor() as nat;
    trust_vc::assert!(x < nat_to_real(a + 1));
}

// upstream `test_chained` => Ok(()). Same-type real chained comparison.
#[trust_vc::ensures(true)]
fn test_chained(n: nat) {
    trust_vc::assert!(0real <= 0real < n as real + 1real < n as real + 2real);
}

// upstream `test_reject_mixed` => Err(err) => assert_vir_error_msg(err, "...").
// Mixed real/int chained comparison is rejected with the upstream diagnostic.
#[trust_vc::ensures(true)]
fn test_reject_mixed() {
    trust_vc::assert!(0real <= 1int <= 2real);
}
