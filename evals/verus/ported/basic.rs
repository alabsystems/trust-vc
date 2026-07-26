// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for early upstream basic.rs cases.
//
// This file intentionally covers only the small assertion, assumption, integer
// arithmetic, assignment, pure short-circuit, delayed-init,
// mutable-parameter, parenthesized block syntax, and simple executable-call
// surface from upstream
// `test1`, `test1_fails`, `test2`, `test2_fails`, `test_assign`,
// `test_assign_mut`, `test_short_circuit`, `test_short_circuit2`,
// `test_short_circuit3`, `test_decl_init_let_pass`, `test_paren`,
// `test_mut_param`, and `test_exec_fun1`, plus boolean-XOR assertion parity.
// It is not a full port of basic.rs — it covers 15 of the 60 upstream cases.
//
// STALENESS WARNING (measured 2026-07-10): this file's coverage lags the ENGINE,
// not the other way round. The previous version of this comment claimed
// "proof-note diagnostics ... remain unsupported here"; that was FALSE.
// `#[trust_vc::proof_note("..")]` and `#[trust_vc::custom_err("..")]` already
// work on an assert (the note renders verbatim as `note: <text>`; `custom_err`
// replaces the message), as does the duplicate rejection "at most one
// `proof_note` attribute is allowed". Several other upstream cases are likewise
// already supported and merely UNPORTED (mode/spec-context diagnostics,
// spec_eq_type_error 1-4, compound-assign, test_ret/test_ret2, destructuring
// fail-close, hide!/test_spec_fn).
//
// So the work this file needs is PORT EXTENSION, not new capability. See the
// manifest `reason` for the measured breakdown and for what is GENUINELY still
// missing (notes are not surfaced on requires/ensures-site failures; the two
// `--no-cheating` option cases; named-return-value collision; rlimit options).
// Every added case must FAITHFULLY reproduce its upstream case's verdict — do
// not map a case to a convenient verdict class to make it pass.

use trust_vc_types::int;

pub const BASIC_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    ("test1", "test1", "verified", 1),
    ("test2", "test2", "verified", 1),
    ("bool_xor", "bool_xor", "verified", 4),
    ("test_exec_fun1", "test_exec_fun1", "verified", 1),
    (
        "test_short_circuit_and",
        "test_short_circuit",
        "verified",
        2,
    ),
    (
        "test_short_circuit_or",
        "test_short_circuit",
        "verified",
        2,
    ),
    (
        "test_decl_init_let_pass",
        "test_decl_init_let_pass",
        "verified",
        1,
    ),
    ("test_paren", "test_paren", "verified", 1),
    (
        "test_mut_param_exec_preserves_original",
        "test_mut_param",
        "verified",
        1,
    ),
    ("test1_fails", "test1_fails", "counterexample", 1),
    ("test2_fails", "test2_fails", "counterexample", 1),
    ("test_assign", "test_assign", "counterexample", 1),
    ("test_assign_mut", "test_assign_mut", "counterexample", 1),
    ("bool_xor_fails", "bool_xor_fails", "counterexample", 1),
    (
        "bool_xor_fails_false_true",
        "bool_xor_fails",
        "counterexample",
        1,
    ),
    (
        "bool_xor_fails_true_false",
        "bool_xor_fails",
        "counterexample",
        1,
    ),
    (
        "bool_xor_fails_false_false",
        "bool_xor_fails",
        "counterexample",
        1,
    ),
    (
        "test_short_circuit2",
        "test_short_circuit2",
        "counterexample",
        2,
    ),
    (
        "test_short_circuit3",
        "test_short_circuit3",
        "counterexample",
        2,
    ),
    (
        "test_mut_param_exec_wrong_postcondition",
        "test_mut_param",
        "counterexample",
        1,
    ),
];

pub fn basic_rs_expected_cases() -> &'static [(&'static str, &'static str, &'static str, usize)] {
    BASIC_RS_EXPECTED_CASES
}

#[trust_vc::ensures(true)]
fn test1() {
    trust_vc::assert!(true);
    trust_vc::assert!(!false);
    trust_vc::assert!(true && true);
    trust_vc::assert!(true || false);
    trust_vc::assert!(true);
}

#[trust_vc::ensures(true)]
fn test1_fails() {
    trust_vc::assert!(true);
    trust_vc::assert!(true && false);
    trust_vc::assert!(false);
    trust_vc::assert!(false);
}

#[trust_vc::spec]
fn basic_test2_f(i: int, j: int) -> bool {
    i <= j
}

#[trust_vc::ensures(true)]
fn test2(b: bool, x: int, y: int, z: int) {
    trust_vc::assert!(b || !b);

    trust_vc::assume!(b);
    trust_vc::assert!(b);

    trust_vc::assert!(x != y || basic_test2_f(x, y) == basic_test2_f(y, x));

    trust_vc::assert!(x + y == y + x);

    trust_vc::assume!(x <= y && y <= z);
    trust_vc::assert!(x <= z);
}

#[trust_vc::ensures(true)]
fn test2_fails(_b: bool, x: int, y: int, z: int) {
    trust_vc::assume!(x <= y && y <= z);
    trust_vc::assert!(x < z);
}

#[trust_vc::ensures(true)]
fn test_assign(a: int, b: int) {
    let c = a + b;
    trust_vc::assert!(c == a + b);

    let d = false;
    trust_vc::assert!(!d);

    trust_vc::assert!(c < a + b);
}

#[trust_vc::ensures(true)]
fn test_assign_mut(a: int, b: int) {
    let mut c = a;
    c = c + b;
    trust_vc::assert!(c == a + b);
    trust_vc::assert!(c == a);
}

#[trust_vc::ensures(true)]
fn bool_xor() {
    trust_vc::assert!((true ^ true) == false);
    trust_vc::assert!((false ^ true) == true);
    trust_vc::assert!((true ^ false) == true);
    trust_vc::assert!((false ^ false) == false);
}

#[trust_vc::ensures(true)]
fn bool_xor_fails() {
    trust_vc::assert!((true ^ true) == true);
}

#[trust_vc::ensures(true)]
fn bool_xor_fails_false_true() {
    trust_vc::assert!((false ^ true) == false);
}

#[trust_vc::ensures(true)]
fn bool_xor_fails_true_false() {
    trust_vc::assert!((true ^ false) == false);
}

#[trust_vc::ensures(true)]
fn bool_xor_fails_false_false() {
    trust_vc::assert!((false ^ false) == true);
}

fn basic_exec_fun1_f(_x: u64) -> u64 {
    5u64
}

fn basic_exec_fun1_g(x: u64) -> u64 {
    basic_exec_fun1_f(x)
}

#[trust_vc::ensures(true)]
fn test_exec_fun1(x: u64) {
    let y = basic_exec_fun1_g(x);
    trust_vc::assert!(y == 5u64);
}

#[trust_vc::ensures(true)]
fn test_short_circuit_and(a: bool, b: bool) {
    let y = a && b;
    let z = a && b;
    let x = if a { 1u64 } else { 0u64 };

    trust_vc::assert!(y == z);
    trust_vc::assert!((x == 1u64) == a);
}

#[trust_vc::ensures(true)]
fn test_short_circuit_or(a: bool, b: bool) {
    let y = a || b;
    let z = a || b;
    let x = if a { 0u64 } else { 1u64 };

    trust_vc::assert!(y == z);
    trust_vc::assert!((x == 1u64) == !a);
}

#[trust_vc::ensures(true)]
fn test_short_circuit2(a: bool, b: bool) {
    let y = a && b;
    let z = a && b;
    let x = if a { 1u64 } else { 0u64 };

    trust_vc::assert!(y == z);
    trust_vc::assert!(x == 0u64);
}

#[trust_vc::ensures(true)]
fn test_short_circuit3(a: bool, b: bool) {
    let y = a && b;
    let z = a && b;
    let x = if a { 1u64 } else { 0u64 };

    trust_vc::assert!(y == z);
    trust_vc::assert!(x == 1u64);
}

#[trust_vc::ensures(true)]
fn test_decl_init_let_pass() {
    let x: u64;
    x = 23u64;
    trust_vc::assert!(x == 23u64);
}

#[trust_vc::ensures(true)]
fn test_paren() {
    {
        {
            {
                {
                    if true {
                        trust_vc::assert!(true);
                    } else {
                    }
                }
            }
        }
    }
    (if true {
        trust_vc::assert!(true);
    } else {
    });
}

#[trust_vc::requires(x < 10u32)]
#[trust_vc::ensures(x < 10u32)]
fn test_mut_param_exec_preserves_original(mut x: u32) {
    trust_vc::assert!(x < 20u32);
    x = 100u32;
    trust_vc::assert!(x == 100u32);
}

#[trust_vc::requires(x < 10u32)]
#[trust_vc::ensures(x == 100u32)]
fn test_mut_param_exec_wrong_postcondition(mut x: u32) {
    trust_vc::assert!(x < 20u32);
    x = 100u32;
    trust_vc::assert!(x == 100u32);
}
