// Example of how tests SHOULD be written to properly verify
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! This file demonstrates the RIGHT way to write verification tests.
//! All tests use VerificationPipeline and check specific outcomes.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

/// Helper: Run a #[trust_vc::proof] function and assert it verifies successfully.
///
/// #[trust_vc::proof] functions auto-verify internally and panic on failure,
/// so this simply calls the proof function — success = no panic.
fn verify_should_pass<F>(proof_fn: F)
where
    F: FnOnce(),
{
    proof_fn();
}

/// Helper: Run a #[trust_vc::proof] function and assert it should NOT verify.
///
/// #[trust_vc::proof] functions auto-verify internally and panic on failure,
/// so we catch that expected panic to confirm verification failed.
fn verify_should_fail<F>(proof_fn: F)
where
    F: FnOnce() + std::panic::UnwindSafe,
{
    let result = std::panic::catch_unwind(proof_fn);
    assert!(result.is_err(), "Proof should NOT verify but it succeeded");
}

mod common;

#[cfg(test)]
mod tests {
    use super::*;

    /// Test basic assertions - both positive and negative cases
    #[test]
    fn test_basic_assertions_properly() {
        common::with_clean_verification(|| {
            // POSITIVE TEST: Valid assertions should verify
            verify_should_pass(|| {
                #[trust_vc::proof]
                fn valid_assertions() {
                    trust_vc::assert!(true);
                    trust_vc::assert!(1 + 1 == 2);
                    trust_vc::assert!(10 > 5);
                }
                valid_assertions();
            });

            // NEGATIVE TEST: Invalid assertions should NOT verify
            verify_should_fail(|| {
                #[trust_vc::proof]
                fn invalid_assertion() {
                    trust_vc::assert!(false);
                }
                invalid_assertion();
            });
        })
    }

    /// Test assumptions and their effect on verification
    #[test]
    fn test_assumptions_properly() {
        common::with_clean_verification(|| {
            // #2258: false assumption → vacuous truth detected → proof fails
            verify_should_fail(|| {
                #[trust_vc::proof]
                fn with_assumption() {
                    trust_vc::assume!(false);
                    // Under false assumption, vacuous truth is now detected
                    trust_vc::assert!(1 == 2);
                }
                with_assumption();
            });

            // NEGATIVE: Without assumption, invalid assertion fails
            verify_should_fail(|| {
                #[trust_vc::proof]
                fn without_assumption() {
                    // No assumption, so this should fail
                    trust_vc::assert!(1 == 2);
                }
                without_assumption();
            });
        })
    }

    /// Every feature needs both positive and negative tests!
    ///
    /// Test naming convention:
    /// - test_FEATURE_properly: Tests both valid and invalid cases
    /// - test_FEATURE_accepts_valid: Positive test only
    /// - test_FEATURE_rejects_invalid: Negative test only
    ///
    /// Always:
    /// 1. Use VerificationPipeline (via helper functions)
    /// 2. Assert specific expected outcomes
    /// 3. Test both success and failure cases
    /// 4. Name tests to match what they verify
    #[test]
    fn test_guidelines() {
        common::with_clean_verification(|| {
            // Guidelines:
            // 1. Always use VerificationPipeline for actual verification
            // 2. Use concrete values to avoid quantifier issues
            // 3. Test both success and failure cases
            // 4. Name tests to match what they verify
            println!("Follow these guidelines for all tests!");
        })
    }
}
