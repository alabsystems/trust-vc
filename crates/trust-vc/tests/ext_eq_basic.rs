// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for extensional equality macros (ext_eq!, ext_ne!).
//!
//! Verifies that ext_eq! and ext_ne! compile and type-check.
//! Actual ay extensional equality verification happens via trust_mc.

use trust_vc::{equal, ext_eq, ext_ne, strict_eq};

// ============================================================================
// ext_eq! tests
// ============================================================================

#[test]
fn test_ext_eq_compiles() {
    // Basic compilation test
    let result = ext_eq!(1, 1);
    assert!(result, "ext_eq! should return true at runtime");
}

#[test]
fn test_ext_eq_integers() {
    // Works with integers
    let a = 42;
    let b = 42;
    let result = ext_eq!(a, b);
    assert!(result);
}

#[test]
fn test_ext_eq_arrays() {
    // Works with arrays
    let arr1 = [1, 2, 3];
    let arr2 = [1, 2, 3];
    let result = ext_eq!(arr1, arr2);
    assert!(result);
}

#[test]
fn test_ext_eq_vectors() {
    // Works with vectors
    let v1 = vec![1, 2, 3, 4, 5];
    let v2 = vec![1, 2, 3, 4, 5];
    let result = ext_eq!(v1, v2);
    assert!(result);
}

#[test]
fn test_ext_eq_slices() {
    // Works with slices
    let arr = [1, 2, 3, 4, 5];
    let s1 = &arr[0..3];
    let s2 = &arr[0..3];
    let result = ext_eq!(s1, s2);
    assert!(result);
}

#[test]
fn test_ext_eq_expression() {
    // Works with expressions
    let x = 10;
    let result = ext_eq!(x + 5, 15);
    assert!(result);
}

// ============================================================================
// ext_ne! tests
// ============================================================================

#[test]
fn test_ext_ne_compiles() {
    // Basic compilation test
    let result = ext_ne!(1, 2);
    assert!(result, "ext_ne! should return true at runtime");
}

#[test]
fn test_ext_ne_integers() {
    // Works with different integers
    let a = 42;
    let b = 43;
    let result = ext_ne!(a, b);
    assert!(result);
}

#[test]
fn test_ext_ne_arrays() {
    // Works with different arrays
    let arr1 = [1, 2, 3];
    let arr2 = [1, 2, 4];
    let result = ext_ne!(arr1, arr2);
    assert!(result);
}

#[test]
fn test_ext_ne_vectors_different_length() {
    // Different length vectors
    let v1 = vec![1, 2, 3];
    let v2 = vec![1, 2, 3, 4];
    let result = ext_ne!(v1, v2);
    assert!(result);
}

#[test]
fn test_strict_eq_compiles() {
    let result = strict_eq!(42, 42);
    assert!(result);
}

#[test]
fn test_equal_alias_compiles() {
    let result = equal!(42, 42);
    assert!(result);
}

// ============================================================================
// Combined tests
// ============================================================================

#[test]
fn test_ext_eq_in_condition() {
    // Can use in conditions
    let a = 5;
    let b = 5;
    if ext_eq!(a, b) {
        // Should enter this branch - test passes by not panicking
    } else {
        panic!("Should not reach here");
    }
}

#[test]
fn test_ext_eq_multiple() {
    // Multiple ext_eq! in sequence
    let x = 10;
    let y = 10;
    let z = 10;
    assert!(ext_eq!(x, y));
    assert!(ext_eq!(y, z));
    assert!(ext_eq!(x, z));
}

#[test]
fn test_ext_eq_with_functions() {
    // Works with function results
    fn double(x: i32) -> i32 {
        x * 2
    }

    let a = 5;
    let result = ext_eq!(double(a), 10);
    assert!(result);
}

#[test]
fn test_ext_eq_nested() {
    // Nested in other constructs
    let arr = [[1, 2], [3, 4]];
    let result = ext_eq!(arr[0], [1, 2]);
    assert!(result);
}
