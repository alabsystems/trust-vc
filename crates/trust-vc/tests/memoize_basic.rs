// Memoize basic tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for #[trust_vc::memoize] attribute.
//!
//! This attribute marks functions for result caching during proof computation,
//! primarily affecting `assert_by_compute!` behavior for recursive functions.
//!
//! At runtime, memoization has no effect - the function executes normally.
//! The caching only applies during verification-time symbolic evaluation.

/// Simple memoized spec function
#[trust_vc::spec]
#[trust_vc::memoize]
fn memoized_spec() -> i32 {
    42
}

/// Memoized recursive function (Fibonacci pattern)
#[trust_vc::decreases(n)]
#[trust_vc::memoize]
#[trust_vc::spec]
fn fib(n: u64) -> u64 {
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fib(n - 1) + fib(n - 2)
    }
}

/// Memoized function with requires
#[trust_vc::spec]
#[trust_vc::memoize]
fn memoized_with_requires(x: i32) -> i32 {
    trust_vc::requires!(x >= 0);
    x + 1
}

/// Memoized function with multiple parameters
#[trust_vc::decreases(m, n)]
#[trust_vc::memoize]
#[trust_vc::spec]
fn ackermann_like(m: u64, n: u64) -> u64 {
    if m == 0 {
        n + 1
    } else if n == 0 {
        // Note: in real Verus, we'd have recursive call here
        // Simplified for testing
        m
    } else {
        m + n
    }
}

/// Memoized function returning Option
#[trust_vc::spec]
#[trust_vc::memoize]
fn memoized_option(x: i32) -> Option<i32> {
    if x > 0 {
        Some(x * 2)
    } else {
        None
    }
}

/// Memoized function with generic type
#[trust_vc::spec]
#[trust_vc::memoize]
fn memoized_generic<T: Default>() -> Option<T> {
    None
}

/// Memoize combined with returns attribute
#[trust_vc::memoize]
#[trust_vc::returns(result)]
fn memoized_with_returns(x: i32) -> i32 {
    trust_vc::requires!(x > 0);
    x * 2
}

/// Memoize on non-spec function (still valid, just no caching effect)
#[trust_vc::memoize]
fn memoized_exec(x: i32) -> i32 {
    x + 1
}

/// Factorial - another classic memoization use case
#[trust_vc::decreases(n)]
#[trust_vc::memoize]
#[trust_vc::spec]
fn factorial(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

/// Sum function with memoization
#[trust_vc::decreases(n)]
#[trust_vc::memoize]
#[trust_vc::spec]
fn sum_to_n(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        n + sum_to_n(n - 1)
    }
}

/// Memoized function with slice parameter
#[trust_vc::spec]
#[trust_vc::memoize]
fn memoized_with_slice(arr: &[i32]) -> usize {
    arr.len()
}

/// Memoized function with boolean result
#[trust_vc::spec]
#[trust_vc::memoize]
fn is_even(n: u64) -> bool {
    n.is_multiple_of(2)
}

// Note: spec functions panic at runtime, so we can't directly test them.
// Instead we test that memoize on exec functions works at runtime.

#[test]
fn memoized_exec_compiles() {
    assert_eq!(memoized_exec(10), 11);
}

#[test]
fn multiple_memoized_exec_calls() {
    // Verify repeated calls work (memoization is verification-time only)
    assert_eq!(memoized_exec(5), 6);
    assert_eq!(memoized_exec(5), 6);
    assert_eq!(memoized_exec(10), 11);
    assert_eq!(memoized_exec(10), 11);
}

#[test]
fn memoize_attribute_compiles() {
    // These test that the attribute syntax compiles correctly.
    // We can't call spec functions at runtime (they panic).
    // This verifies the proc macro expansion is valid.
    let _ = std::any::type_name_of_val(&memoized_spec);
    let _ = std::any::type_name_of_val(&fib);
    let _ = std::any::type_name_of_val(&memoized_with_requires);
    let _ = std::any::type_name_of_val(&factorial);
}

#[test]
fn memoize_with_decreases_compiles() {
    // Functions with both memoize and decreases should compile
    let _ = std::any::type_name_of_val(&fib);
    let _ = std::any::type_name_of_val(&factorial);
    let _ = std::any::type_name_of_val(&sum_to_n);
}

#[test]
fn memoize_with_generics_compiles() {
    // Generic memoized functions should compile
    let _ = std::any::type_name_of_val(&memoized_generic::<i32>);
    let _ = std::any::type_name_of_val(&memoized_generic::<bool>);
}

#[test]
fn memoize_with_options_compiles() {
    // Memoized functions returning Option should compile
    let _ = std::any::type_name_of_val(&memoized_option);
}

#[test]
fn memoize_combined_attributes_compile() {
    // Memoize combined with other attributes should compile
    let _ = std::any::type_name_of_val(&memoized_with_returns);
    let _ = std::any::type_name_of_val(&memoized_with_requires);
}

#[test]
fn memoize_not_ghost_for_exec() {
    // Unlike spec functions, memoized exec functions should NOT panic
    use std::panic::catch_unwind;

    let result = catch_unwind(|| memoized_exec(42));
    assert!(result.is_ok(), "memoized exec functions should not panic");
    assert_eq!(result.unwrap(), 43);
}
