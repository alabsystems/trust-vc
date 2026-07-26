// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test that trust_vc::assert! has consistent behavior in all modes.
//!
//! Issue #944: trust_vc::assert! has inconsistent behavior between proof and normal mode

use trust_vc::proof;

mod common;

#[test]
fn test_assert_collects_vc_in_test_mode() {
    common::with_clean_verification(|| {
        // In test mode, assertions should collect VCs, not panic
        // This allows negative testing to work
        trust_vc::assert!(1 + 1 == 3); // Should NOT panic in test mode

        // If we reach here, the test passes (no runtime panic)
    })
}

#[test]
#[should_panic(expected = "Proof verification")]
fn test_assert_in_proof_function_no_panic() {
    common::with_clean_verification(|| {
        // #[proof] auto-verifies in test mode — false assertion panics (#2274)
        #[proof]
        fn proof_with_false_assert() {
            trust_vc::assert!(1 + 1 == 3);
        }

        proof_with_false_assert();
    })
}

#[test]
fn test_assert_passes_in_normal_function() {
    common::with_clean_verification(|| {
        // Normal function - should not panic on true assertion
        trust_vc::assert!(1 + 1 == 2);
        // Test passes if we reach here
    })
}

#[test]
fn test_assert_passes_in_proof_function() {
    common::with_clean_verification(|| {
        // Proof function - should not panic on true assertion
        #[proof]
        fn proof_with_true_assert() {
            trust_vc::assert!(1 + 1 == 2); // Should not panic
        }

        proof_with_true_assert();
        // Test passes if we reach here
    })
}

#[test]
fn test_assert_collects_obligations_in_both_modes() {
    common::with_clean_verification(|| {
        use trust_vc_core::verify_macro::get_context;

        // Test normal mode
        trust_vc::assert!(2 > 1);
        let context = get_context();
        std::assert!(
            context.is_some(),
            "Should collect obligation in normal mode"
        );
        assert_eq!(
            context.unwrap().obligations().len(),
            1,
            "Should have one obligation"
        );

        // Test proof mode
        #[proof]
        fn proof_with_assert() {
            trust_vc::assert!(3 > 2);
        }
        proof_with_assert();

        let context = get_context();
        std::assert!(context.is_some(), "Should collect obligation in proof mode");
        std::assert!(
            !context.unwrap().obligations().is_empty(),
            "Should have collected obligations"
        );
    })
}

#[test]
fn test_complex_assertion_consistency() {
    common::with_clean_verification(|| {
        // Test normal function with variables
        let _x = 5;
        let _y = 10;
        trust_vc::assert!(_x < _y);

        // Test proof function separately with clear context
        #[proof]
        fn proof_with_complex_assert() {
            // Use constants to avoid variable parsing issues
            trust_vc::assert!(5 < 10);
        }

        proof_with_complex_assert();

        // Both should succeed without panic
    })
}

#[test]
#[should_panic(expected = "Proof verification")]
fn test_assert_no_runtime_panic_in_test_mode() {
    common::with_clean_verification(|| {
        // #[proof] auto-verifies in test mode — false assertion panics (#2274)
        #[proof]
        fn proof_with_failing_assert() {
            trust_vc::assert!(false);
        }

        proof_with_failing_assert();
    })
}
