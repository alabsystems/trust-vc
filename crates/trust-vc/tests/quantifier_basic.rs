// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Basic quantifier tests for trust_vc.
//!
//! Tests that forall! and exists! macros compile and type-check correctly.
//! Inline verification results depend on ay solver capabilities (may return
//! Unknown for quantified BV formulas), so these tests only assert compilation,
//! not verification results. Use pipeline tests for verification assertions.

use trust_vc::{exists, forall};

fn trigger_predicate(_: i32) -> bool {
    true
}

#[test]
fn test_forall_compiles() {
    // Universal quantifier should compile; inline result depends on ay capabilities
    let _result = forall!(|x: i32| x == x);
}

#[test]
fn test_exists_compiles() {
    // Existential quantifier should compile
    let _result = exists!(|x: i32| x > 0);
}

#[test]
#[allow(clippy::overly_complex_bool_expr)] // Testing tautology specifically
fn test_forall_with_implication() {
    // Common pattern: forall with implication
    let _result = forall!(|x: i32| x > 0 || x <= 0);
}

#[test]
fn test_exists_with_conjunction() {
    // Common pattern: exists with conjunction
    let _result = exists!(|x: i32| x > 0 && x < 10);
}

#[test]
fn test_forall_multiple_vars() {
    // Multiple bound variables using separate closure params
    let _result = forall!(|x: i32, y: i32| x + y == y + x);
}

#[test]
fn test_exists_multiple_vars() {
    // Multiple bound variables using separate closure params
    let _result = exists!(|x: i32, y: i32| x * y == 0);
}

#[test]
fn test_forall_with_usize() {
    // Array index type - common in specifications
    let _result = forall!(|i: usize| i + 1 > 0);
}

#[test]
#[rustfmt::skip]
fn test_forall_with_expression_trigger_compiles() {
    let _result = forall!(|x: i32| #[trigger] trigger_predicate(x) && x == x);
}

#[test]
fn test_quantifier_closure_type_checked() {
    // The closure body is type-checked even though never called
    // This tests that the macro preserves type checking

    // Would fail to compile if type-checking didn't work:
    // forall!(|x: i32| x + "string")  // Would be compile error

    // This should compile:
    let _valid = forall!(|x: i32| x.abs() >= 0);
}
