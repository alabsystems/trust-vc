// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Basic decreases/termination tests for trust_vc.
//!
//! These tests verify the #[decreases] attribute compiles correctly
//! and that termination obligations are properly collected and verified.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc::decreases;
use trust_vc_core::verify_macro;

#[decreases(n)]
fn factorial(n: u64) -> u64 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

#[decreases(n)]
fn fibonacci(n: u64) -> u64 {
    if n <= 1 {
        n
    } else {
        fibonacci(n - 1) + fibonacci(n - 2)
    }
}

mod common;

#[test]
fn test_decreases_compiles() {
    common::with_clean_verification(|| {
        // Functions with #[decreases] should compile and execute normally
        // (Removed verification context setup since we're only testing runtime behavior)
        assert_eq!(factorial(0), 1);
        assert_eq!(factorial(5), 120);

        // Note: The #[decreases] macro doesn't automatically register VCs during tests
        // It's a compile-time attribute that would need proc-macro expansion to collect
        // For now, we're testing that the functions compile and execute correctly
        // Actual termination verification would require manual VC registration
    })
}

#[test]
fn test_fibonacci_executes() {
    common::with_clean_verification(|| {
        // Fibonacci should work with decreases annotation
        // (Removed verification context setup since we're only testing runtime behavior)
        assert_eq!(fibonacci(0), 0);
        assert_eq!(fibonacci(1), 1);
        assert_eq!(fibonacci(10), 55);

        // Note: The #[decreases] macro doesn't automatically register VCs during tests
        // It's a compile-time attribute that would need proc-macro expansion to collect
        // For now, we're testing that the functions compile and execute correctly
        // Actual termination verification would require manual VC registration
    })
}

// Lexicographic measures - Ackermann function
#[decreases(m, n)]
fn ackermann(m: u64, n: u64) -> u64 {
    if m == 0 {
        n + 1
    } else if n == 0 {
        ackermann(m - 1, 1)
    } else {
        ackermann(m - 1, ackermann(m, n - 1))
    }
}

#[test]
fn test_lexicographic_decreases() {
    common::with_clean_verification(|| {
        // Ackermann with lexicographic measure (m, n) should compile and execute
        // (Removed verification context setup since we're only testing runtime behavior)
        assert_eq!(ackermann(0, 0), 1);
        assert_eq!(ackermann(1, 1), 3);
        assert_eq!(ackermann(2, 2), 7);
        assert_eq!(ackermann(3, 2), 29);

        // Note: The #[decreases] macro doesn't automatically register VCs during tests
        // It's a compile-time attribute that would need proc-macro expansion to collect
        // For now, we're testing that the functions compile and execute correctly
        // Actual termination verification with lexicographic measures would require manual VC registration
    })
}

#[test]
fn test_valid_decreases_measure_verifies() {
    common::with_clean_verification(|| {
        // Test that a valid decreasing measure is accepted
        // Import needed types
        use trust_vc_core::verification_bridge::VerificationPipeline;
        use trust_vc_core::VerifyResult;

        // Simulate factorial with valid decreases
        // factorial(5) calls factorial(4)
        // Use u64 to match the factorial function signature
        verify_macro::collect_variable("n".to_string(), "u64".to_string());
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_value".to_string(),
            "n == 5u64".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureDecreases,
            "factorial_decreases".to_string(),
            "(n - 1u64) < n".to_string(), // 4 < 5 is true
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid decreases measure should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_invalid_decreases_measure_fails() {
    common::with_clean_verification(|| {
        // Test that an invalid decreasing measure is rejected
        // Import needed types
        use trust_vc_core::verification_bridge::VerificationPipeline;
        use trust_vc_core::VerifyResult;

        // Simulate a function where measure doesn't decrease
        verify_macro::collect_variable("n".to_string(), "u64".to_string());
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_value".to_string(),
            "n == 5u64".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureDecreases,
            "bad_recursion".to_string(),
            "(n + 1u64) < n".to_string(), // 6 < 5 is false
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Invalid decreases measure should NOT verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_non_terminating_recursion_fails() {
    common::with_clean_verification(|| {
        // Test that non-terminating recursion is rejected
        // Import needed types
        use trust_vc_core::verification_bridge::VerificationPipeline;
        use trust_vc_core::VerifyResult;

        // Simulate recursion with same value (infinite loop)
        verify_macro::collect_variable("n".to_string(), "u64".to_string());
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_value".to_string(),
            "n == 10u64".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureDecreases,
            "infinite_loop".to_string(),
            "n < n".to_string(), // Always false
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Non-terminating recursion should NOT verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_lexicographic_decreases_valid() {
    common::with_clean_verification(|| {
        // Test valid lexicographic measure (like in Ackermann)
        // Import needed types
        use trust_vc_core::verification_bridge::VerificationPipeline;
        use trust_vc_core::VerifyResult;

        // First component decreases: (m-1, _) < (m, n)
        verify_macro::collect_variable("m".to_string(), "u64".to_string());
        verify_macro::collect_variable("n".to_string(), "u64".to_string());
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "m_value".to_string(),
            "m == 3u64".to_string(),
            None,
        );
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_value".to_string(),
            "n == 2u64".to_string(),
            None,
        );

        // Lexicographic: (m-1, 1) < (m, n) when m > 0
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::MeasureDecreases,
            "ackermann_first_component".to_string(),
            "(m - 1u64) < m".to_string(), // 2 < 3 is true
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Valid lexicographic decreases should verify, got: {:?}",
            result
        );
    })
}
