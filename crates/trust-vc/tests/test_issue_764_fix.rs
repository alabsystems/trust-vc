// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test to verify issue #764 is fixed - assert_by! with let statements

use trust_vc::assert_by;

#[test]
fn test_assert_by_with_let_statements() {
    // This is the exact example from issue #764
    let a = 3;
    let b = 5;

    assert_by! {
        let sum = a + b;
        sum == 8
    };

    // If this test passes without parse errors, issue #764 is fixed
}

#[test]
fn test_complex_block_with_multiple_lets() {
    assert_by! {
        let x = 10;
        let y = 20;
        let z = x + y;
        let result = z * 2;
        result == 60
    };
}

#[test]
fn test_block_with_computations() {
    let base = 5;

    assert_by! {
        let doubled = base * 2;
        let tripled = base * 3;
        let sum = doubled + tripled;
        sum == base * 5  // 10 + 15 == 25
    };
}
