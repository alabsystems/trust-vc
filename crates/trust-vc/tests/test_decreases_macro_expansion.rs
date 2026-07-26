// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Macro-level test for issue #1353: Test decreases macro compilation
//!
//! VERIFICATION LEVEL: MACRO EXPANSION
//! Tests that the decreases macro compiles with valid and invalid measures.
//! Does NOT invoke ay verification — only tests macro compilation.
//!
//! Actual ay verification of decreases measures blocked on #1353.

use trust_vc::decreases;

// This test is expected to fail at compile-time or during verification
// If it compiles and runs without error, we have a soundness bug

#[test]
fn test_macro_invalid_decreases_increasing() {
    // This function has an INVALID decreases measure
    // It calls itself with n+1, which increases instead of decreases
    #[decreases(n)]
    fn bad_infinite_loop(n: u64) -> u64 {
        if n >= 100 {
            100
        } else {
            // BUG: Calls with n+1 which INCREASES the measure
            bad_infinite_loop(n + 1)
        }
    }

    // Once decreases verification is complete (#1353), this should fail.
    // For now we just test that the macro compiles
}

#[test]
fn test_macro_invalid_decreases_same() {
    // This function has an INVALID decreases measure
    // It calls itself with the same value
    #[decreases(n)]
    fn bad_no_progress(n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            // BUG: Calls with same value, no progress
            bad_no_progress(n)
        }
    }

    // Once decreases verification is complete (#1353), this should fail.
    // For now we just test that the macro compiles
}

#[test]
fn test_macro_valid_decreases_works() {
    // Control test: valid decreases should work
    #[decreases(n)]
    fn good_factorial(n: u64) -> u64 {
        if n == 0 {
            1
        } else {
            // VALID: Calls with n-1 which properly decreases
            n * good_factorial(n - 1)
        }
    }

    // This should work without panic
    let result = good_factorial(5);
    assert_eq!(result, 120); // 5! = 120
}
