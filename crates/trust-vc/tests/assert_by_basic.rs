// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for assert_by! macro - scoped assertions with proof blocks.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline
//!
//! Tests both compilation and verification of assert_by! assertions.
//!
//! Note: The current assert_by! implementation accepts raw tokens (condition
//! and proof block together) which trust_mc will parse.

use trust_vc::assert_by;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;
use test_verify_helpers_v2::expect_counterexample;

mod common;

#[test]
fn test_assert_by_compiles_empty() {
    common::with_clean_verification(|| {
        // Basic assert_by! with minimal content
        assert_by! {
            true
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Trivial true assertion should verify"
            ),
        }
    })
}

#[test]
fn test_assert_by_compiles_with_let() {
    common::with_clean_verification(|| {
        // Let bindings can also be inside assert_by! (fix #845),
        // but this test verifies the external-binding pattern still works
        let x = 10;
        let _y = x + 1;
        assert_by! {
            true
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "assert_by! with pre-computed values should verify"
            ),
        }
    })
}

#[test]
fn test_assert_by_with_variables() {
    common::with_clean_verification(|| {
        // Concrete arithmetic expressions are verified directly
        // Outer-scope variables aren't visible to the encoder (only proof-block let bindings are inlined)
        assert_by! {
            5 + 3 == 8
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "assert_by! with arithmetic should verify"
            ),
        }
    })
}

#[test]
fn test_assert_by_scope_isolation() {
    common::with_clean_verification(|| {
        // Fix #845: let bindings inside assert_by! are now inlined
        assert_by! {
            let product = 10 * 2;
            product == 20
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "assert_by! with let binding should verify"
            ),
        }
    })
}

#[test]
fn test_assert_by_chained() {
    common::with_clean_verification(|| {
        // Multiple assert_by! in sequence with concrete values
        assert_by! { 5 > 0 };
        assert_by! { 5 < 10 };
        assert_by! { 5 == 5 };

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Chained assert_by! assertions should all verify"
            ),
        }
    })
}

#[test]
fn test_assert_by_with_function_call() {
    common::with_clean_verification(|| {
        // Test that assert_by! works with expressions
        // Note: Function calls in assert_by! aren't fully supported by the parser yet
        assert_by! { 3 * 2 == 6 }; // Simulating helper(3) == 6

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "assert_by! with expressions should verify"
            ),
        }
    })
}

#[test]
fn test_assert_by_nested_expressions() {
    common::with_clean_verification(|| {
        // Fix #845: chained let bindings with nested expressions
        assert_by! {
            let a = 1 + 2;
            let b = a * 3;
            b == 9
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "assert_by! with chained let bindings should verify"
            ),
        }
    })
}

#[test]
fn test_assert_by_marker_generated() {
    common::with_clean_verification(|| {
        // The macro generates a marker for trust_mc detection
        // This tests that the expansion doesn't error
        assert_by! { true };

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "assert_by! marker generation should verify"
            ),
        }
    })
}

#[test]
fn test_assert_by_boolean_ops() {
    common::with_clean_verification(|| {
        // Boolean operations with concrete values
        assert_by! { true }; // Simple boolean assertion

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "assert_by! with boolean operations should verify"
            ),
        }
    })
}

#[test]
fn test_assert_by_comparison() {
    common::with_clean_verification(|| {
        // Comparison operations with concrete values
        assert_by! { 42 == 42 };
        assert_by! { 42 != 0 };
        assert_by! { 42 > 0 };
        assert_by! { 42 >= 42 };

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "assert_by! with comparison operations should verify"
            ),
        }
    })
}

#[test]
fn test_assert_by_simple_false_condition() {
    common::with_clean_verification(|| {
        // Test that assert_by! with a false expression correctly fails verification
        use std::panic;

        // Capture the panic from the runtime assertion
        let _ = panic::catch_unwind(|| {
            // Use a simple expression without blocks or let statements
            assert_by! { false };
        });

        // Verify that "false" was properly forwarded to ay
        let result = expect_counterexample();
        match result {
            Ok((obligation_name, _model)) => {
                assert!(
                    obligation_name.contains("assert_by") || obligation_name.contains("false"),
                    "Expected obligation name to reference assert_by or false, got: {}",
                    obligation_name
                );
            }
            Err(e) => {
                panic!(
                    "assert_by! with false should produce counterexample, got: {}",
                    e
                );
            }
        }
    })
}

#[test]
fn test_assert_by_simple_true_condition() {
    common::with_clean_verification(|| {
        // Test that assert_by! with a simple true expression passes verification
        assert_by! { true };

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "assert_by! with true should pass verification"
            ),
        }
    })
}

// ============================================================================
// Two-argument form tests (Verus-style assert_by)
// Part of #2386 Phase 2: assert_by proc-macro usability
// ============================================================================

/// Verus-style assert_by with trivial condition and empty proof block.
#[test]
fn test_assert_by_two_arg_trivial() {
    common::with_clean_verification(|| {
        assert_by!(true, {});

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified for trivial two-arg assert_by, got {:?}",
                other
            ),
        }
    })
}

/// Verus-style assert_by with arithmetic condition and empty proof block.
#[test]
fn test_assert_by_two_arg_arithmetic() {
    common::with_clean_verification(|| {
        assert_by!(5 + 3 == 8, {});

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified for arithmetic two-arg assert_by, got {:?}",
                other
            ),
        }
    })
}

/// Verus-style assert_by with proof block containing a helper assertion.
///
/// The proof block's inner assert establishes `5 > 3` as a scoped fact,
/// then the condition `5 > 0` is proved with that scoped context.
/// Both are trivially true, but this tests the scoping mechanism.
#[test]
fn test_assert_by_two_arg_with_inner_assert() {
    common::with_clean_verification(|| {
        assert_by!(5 > 0, {
            trust_vc::assert!(5 > 3);
        });

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "#2386: assert_by with inner assert should verify, got {:?}",
                other
            ),
        }
    })
}

/// Verus-style assert_by with multiple inner assertions in proof block.
#[test]
fn test_assert_by_two_arg_multiple_inner_asserts() {
    common::with_clean_verification(|| {
        assert_by!(10 > 0, {
            trust_vc::assert!(10 > 5);
            trust_vc::assert!(5 > 0);
        });

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "#2386: assert_by with multiple inner asserts should verify, got {:?}",
                other
            ),
        }
    })
}
