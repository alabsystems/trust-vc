// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Edge case tests for proof_block! macro

use trust_vc::proof_block;

#[test]
fn test_proof_block_mutable_capture() {
    // This test ensures proof_block can capture mutable references
    // even though it doesn't execute
    let mut value = 42;

    proof_block! {
        // This should type-check even with mutable reference
        value += 1;
        assert_eq!(value, 43);
    }

    // Value should remain unchanged since proof_block doesn't execute
    assert_eq!(value, 42, "proof_block should not modify value");
}

#[test]
fn test_proof_block_early_return() {
    // Test that early returns in proof_block don't affect the outer function
    fn function_with_proof_block() -> i32 {
        proof_block! {
            // This return should not affect the outer function
            return 999;
        }

        // This should be the actual return value
        42
    }

    assert_eq!(function_with_proof_block(), 42);
}

#[test]
fn test_proof_block_with_unsafe() {
    // Test that proof_block can contain unsafe code
    let ptr = 42 as *const i32;

    proof_block! {
        // SAFETY: This block is erased at runtime by `proof_block!` (ghost code),
        // so the invalid pointer dereference never executes. The unsafe block
        // exists solely to test that `proof_block!` can syntactically contain
        // unsafe code without affecting runtime behavior.
        unsafe {
            // This would dereference a bad pointer if executed
            let _ = *ptr;
        }
    }

    // Test passes if we reach here without segfault - no assertion needed
}

#[test]
fn test_proof_block_shadowing() {
    let x = 10;

    proof_block! {
        // Variable shadowing should work
        let x = 20;
        assert_eq!(x, 20);

        // Inner scope shadowing
        {
            let x = 30;
            assert_eq!(x, 30);
        }
    }

    // Original x should be unchanged
    assert_eq!(x, 10);
}

#[test]
fn test_proof_block_type_inference() {
    proof_block! {
        // Type inference should work
        let values = [1, 2, 3];
        let sum: i32 = values.iter().sum();
        assert_eq!(sum, 6);

        // Generic functions should work
        fn identity<T>(x: T) -> T { x }
        let result = identity(42);
        assert_eq!(result, 42);
    }

    // Test passes if type checking succeeds - no assertion needed
}
