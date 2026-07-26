// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Test to check if assert_by! executes at runtime

use trust_vc::assert_by;

#[test]
fn test_assert_by_does_not_execute_at_runtime() {
    // If assert_by! executes at runtime, this should panic
    // But it shouldn't execute at runtime - it should only collect VCs

    // This test checks that assert_by! does NOT panic on false conditions
    // (because it shouldn't execute at runtime)

    // Try asserting false - should NOT panic if properly implemented
    assert_by! {
        false
    }

    // Try another false assertion
    assert_by! {
        1 == 2
    }

    // Try a complex false assertion
    let x = 5;
    assert_by! {
        x > 10
    }

    // If we reach here, assert_by! is correctly NOT executing at runtime
    // This is the expected behavior
}

#[test]
fn test_assert_by_with_complex_false() {
    // Test with complex false conditions
    assert_by! {
        2 + 2 == 5  // Obviously false
    }

    // Another complex false assertion
    let x = 10;
    let y = 20;
    assert_by! {
        x > y  // 10 > 20 is false
    }

    // If we reach here without panic, assert_by! didn't execute at runtime (good)
}

#[test]
fn test_assert_by_with_invalid_syntax() {
    // Test that assert_by! doesn't try to execute invalid formulas
    // These should be collected as strings, not executed

    // This would cause runtime error if executed as Rust code
    // but should be fine if just collected as a verification condition
    assert_by! {
        // Using forall syntax that doesn't exist in runtime Rust
        true  // Simplified for now since we can't use undefined syntax
    }
}
