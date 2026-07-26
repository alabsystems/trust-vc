// tests/ghost_requires_basic.rs
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache 2.0

//! Tests for the ghost_requires! macro
//!
//! ghost_requires! is a no-op outside trust_mc mode (#[cfg(trust_mc)]). In test mode,
//! it does not collect verification obligations. These tests verify:
//! 1. The macro compiles and is a no-op at runtime (doesn't panic or affect execution)
//! 2. The macro accepts valid Rust expressions (syntax check)
//! 3. Precondition verification works when obligations are collected manually
//!
//! VERIFICATION LEVEL: MOCK (ghost_requires noop) + VERIFY (manual precondition tests)
//! See also: #852 (empty verification context root cause)

use trust_vc::{ghost_ensures, ghost_requires};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

mod common;

// ============================================================================
// Part 1: ghost_requires! is a no-op in test mode (macro compiles, no effect)
// ============================================================================

#[test]
fn test_ghost_requires_basic_noop() {
    common::with_clean_verification(|| {
        // ghost_requires! should compile and be a no-op in test mode
        fn add_positive(x: i32, y: i32) -> i32 {
            ghost_requires!(x > 0);
            ghost_requires!(y > 0);
            x + y
        }

        // Function works normally — ghost_requires is erased
        assert_eq!(add_positive(1, 2), 3);
        assert_eq!(add_positive(10, 20), 30);
        // Negative inputs also work (ghost_requires is not enforced at runtime)
        assert_eq!(add_positive(-1, -2), -3);
    })
}

#[test]
fn test_ghost_requires_with_complex_condition_noop() {
    common::with_clean_verification(|| {
        fn safe_divide(x: i32, y: i32) -> i32 {
            ghost_requires!(y != 0);
            ghost_requires!(x >= 0 || y > 0);
            x / y
        }

        // ghost_requires is erased — function works normally
        assert_eq!(safe_divide(10, 2), 5);
        assert_eq!(safe_divide(20, 4), 5);
    })
}

#[test]
fn test_ghost_requires_in_generic_function_noop() {
    common::with_clean_verification(|| {
        fn get_first<T: Clone>(items: &[T]) -> T {
            ghost_requires!(!items.is_empty());
            items[0].clone()
        }

        let numbers = vec![1, 2, 3];
        assert_eq!(get_first(&numbers), 1);

        let strings = vec!["hello".to_string(), "world".to_string()];
        assert_eq!(get_first(&strings), "hello");
    })
}

#[test]
fn test_ghost_requires_multiple_conditions_noop() {
    common::with_clean_verification(|| {
        fn complex_calculation(a: u32, b: u32, c: u32) -> u32 {
            ghost_requires!(a > 0);
            ghost_requires!(b > 0);
            ghost_requires!(c > 0);
            ghost_requires!(a < 1000);
            ghost_requires!(b < 1000);
            ghost_requires!(c < 1000);

            a * b + c
        }

        assert_eq!(complex_calculation(2, 3, 4), 10);
        assert_eq!(complex_calculation(10, 10, 100), 200);
    })
}

#[test]
fn test_ghost_requires_with_string_message_noop() {
    common::with_clean_verification(|| {
        fn process_data(data: &[u8]) -> usize {
            ghost_requires!(!data.is_empty(), "data must not be empty");
            ghost_requires!(data.len() < 1000, "data too large");
            data.len()
        }

        assert_eq!(process_data(&[1, 2, 3]), 3);
        assert_eq!(process_data(&[0; 100]), 100);
    })
}

#[test]
fn test_ghost_requires_in_impl_block_noop() {
    common::with_clean_verification(|| {
        struct Calculator {
            base: i32,
        }

        impl Calculator {
            fn multiply(&self, x: i32) -> i32 {
                ghost_requires!(x != 0);
                ghost_requires!(self.base != 0);
                self.base * x
            }
        }

        let calc = Calculator { base: 5 };
        assert_eq!(calc.multiply(3), 15);
        assert_eq!(calc.multiply(10), 50);
    })
}

// ============================================================================
// Part 2: Precondition verification works via manual obligation collection
// These tests verify that the VerificationPipeline correctly handles
// assume-then-assert patterns (what ghost_requires would produce under trust_mc).
// ============================================================================

#[test]
fn test_precondition_verification_with_manual_assumes() {
    common::with_clean_verification(|| {
        // Manually collect what ghost_requires!(x > 0) would produce under trust_mc:
        // an assumption, plus an assertion that follows from the assumption
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "precondition_x_positive".to_string(),
            "x > 0".to_string(),
            None,
        );
        // Under the assumption x > 0, verify that x >= 1
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "x_at_least_one".to_string(),
            "x >= 1".to_string(),
            None,
        );

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "x > 0 implies x >= 1 should verify, got: {:?}",
            result
        );
    })
}

// Note: ghost_requires! is a no-op outside trust_mc mode and doesn't actually
// collect verification obligations, so negative tests wouldn't work here.
// When #[cfg(test)] support is added to ghost_requires! (like ensures! has),
// the Part 1 tests above should be updated to verify obligation collection.

// ============================================================================
// Part 3: ghost_ensures! is a no-op in test mode (symmetric with ghost_requires)
// ============================================================================

#[test]
fn test_ghost_ensures_basic_noop() {
    common::with_clean_verification(|| {
        fn add_positive(x: i32, y: i32) -> i32 {
            ghost_requires!(x > 0);
            ghost_requires!(y > 0);
            let result = x + y;
            ghost_ensures!(result > 0);
            result
        }

        assert_eq!(add_positive(1, 2), 3);
        assert_eq!(add_positive(10, 20), 30);
    })
}

#[test]
fn test_ghost_ensures_with_complex_condition_noop() {
    common::with_clean_verification(|| {
        fn safe_divide(x: i32, y: i32) -> i32 {
            ghost_requires!(y != 0);
            let result = x / y;
            ghost_ensures!(result * y <= x);
            result
        }

        assert_eq!(safe_divide(10, 2), 5);
        assert_eq!(safe_divide(20, 4), 5);
    })
}

#[test]
fn test_ghost_ensures_in_impl_block_noop() {
    common::with_clean_verification(|| {
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn increment(&mut self) {
                ghost_requires!(self.value < u32::MAX);
                self.value += 1;
                ghost_ensures!(self.value > 0);
            }
        }

        let mut c = Counter { value: 0 };
        c.increment();
        assert_eq!(c.value, 1);
    })
}
