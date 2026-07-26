// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Basic tests for the old! macro (pre-state values in postconditions).
//!
//! Tests that old! compiles and evaluates correctly at runtime.
//! Actual pre-state tracking happens during ay verification via trust_mc.

use trust_vc::old;

#[test]
fn test_old_evaluates_expression() {
    // At runtime, old! just evaluates its expression
    let x = 42;
    let result = old!(x);
    assert_eq!(result, 42);
}

// test_old_with_arithmetic_basic removed: old!(x + 5) was unsound passthrough (#1836).
// Complex expressions in old!() now correctly produce a compile error.

#[test]
fn test_old_with_reference() {
    let x = 42;
    let r = &x;
    let result = old!(*r);
    assert_eq!(result, 42);
}

#[test]
fn test_old_with_mutable_value() {
    // Demonstrates the intended use case: comparing pre and post state
    let mut x = 10;
    let pre_value = old!(x);
    x += 5;
    assert_eq!(pre_value, 10);
    assert_eq!(x, 15);
}
