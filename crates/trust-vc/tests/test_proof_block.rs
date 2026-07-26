// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test that proof_block! macro properly type-checks without execution at runtime

use trust_vc::proof_block;

#[test]
fn test_proof_block_type_checks() {
    // The proof block should type-check but not execute
    let mut counter = 0;

    proof_block! {
        // This code should be type-checked but not executed
        counter += 1;
        assert!(counter == 1, "This should not execute at runtime");
    }

    // Counter should still be 0 since proof_block doesn't execute
    assert_eq!(counter, 0, "proof_block should not execute at runtime");
}

#[test]
fn test_proof_block_with_lemma_call() {
    fn lemma_addition_commutes(_a: i32, _b: i32) {
        // Lemma body (would contain proof in real usage)
    }

    let x = 5;
    let y = 10;

    proof_block! {
        lemma_addition_commutes(x, y);
    }

    // Test passes if compilation succeeds - proof block is properly erased
}

#[test]
fn test_proof_block_with_complex_expressions() {
    let vec = [1, 2, 3];

    proof_block! {
        // Complex expressions should type-check
        let sum: i32 = vec.iter().sum();
        assert!(sum == 6);

        // This would panic if executed, but it shouldn't execute
        panic!("This should not execute!");
    }

    // Test passes if we reach here - proof block was properly erased
}

#[test]
fn test_proof_block_captures_variables() {
    let x = 42;
    let mut y = 0;

    proof_block! {
        // Should be able to capture variables from outer scope
        y = x * 2;
    }

    // y should still be 0 since proof_block doesn't execute
    assert_eq!(y, 0, "proof_block should not modify captured variables");
}
