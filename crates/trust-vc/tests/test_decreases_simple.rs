// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Simple test for decreases macro - verifies basic functionality
//!
//! VERIFICATION LEVEL: BASIC
//! Tests that the decreases macro compiles and generates obligations

use trust_vc::decreases;

#[test]
fn test_decreases_macro_compiles() {
    // Test that the decreases macro at least compiles
    #[decreases(n)]
    fn simple_countdown(n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            simple_countdown(n - 1)
        }
    }

    // Call the function to ensure it compiles and runs
    let result = simple_countdown(3);
    assert_eq!(result, 0);
}

#[test]
fn test_decreases_with_multiple_args() {
    #[decreases(a, b)]
    fn lexicographic(a: u64, b: u64) -> u64 {
        if a == 0 {
            b
        } else if b == 0 {
            lexicographic(a - 1, 10)
        } else {
            lexicographic(a, b - 1)
        }
    }

    let result = lexicographic(2, 3);
    assert_eq!(result, 10); // Returns b when a == 0, which is 10 from the recursion
}

#[test]
fn test_decreases_no_recursion() {
    // Functions without recursion should work fine
    #[decreases(n)]
    fn no_recursion(n: u64) -> u64 {
        n * 2
    }

    let result = no_recursion(5);
    assert_eq!(result, 10);
}
