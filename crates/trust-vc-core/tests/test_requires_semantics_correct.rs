//! Test that demonstrates correct Requires semantics in function body verification
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! In function body verification, Requires is an ASSUMPTION (precondition),
//! not an assertion. This is standard Hoare logic semantics.

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verify_macro::{collect_obligation, collect_variable, verify_collected};
use trust_vc_core::VerifyResult;

#[test]
fn test_requires_enables_assertion_proof() {
    // Classic Hoare logic: assume precondition, prove postcondition
    common::with_clean_verification(|| {
        // Declare a variable
        collect_variable("x".to_string(), "i32".to_string());

        // Requires: x > 0 && x < 1000 (bounded to prevent BV32 overflow in x + 1)
        collect_obligation(
            ObligationKind::Requires,
            "x_positive".to_string(),
            "x > 0 && x < 1000".to_string(),
            Some("test:1:1".to_string()),
        );

        // Assert: x + 1 > 1 (provable given 0 < x < 1000, no overflow)
        collect_obligation(
            ObligationKind::Assert,
            "x_plus_one_gt_one".to_string(),
            "x + 1 > 1".to_string(),
            Some("test:2:1".to_string()),
        );

        let result = verify_collected();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Given requires(x > 0 && x < 1000), assert(x + 1 > 1) should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_false_proves_anything() {
    // Principle of explosion: from false, anything follows
    common::with_clean_verification(|| {
        // Requires: false (unreachable function)
        collect_obligation(
            ObligationKind::Requires,
            "unreachable".to_string(),
            "false".to_string(),
            Some("test:1:1".to_string()),
        );

        // Assert: 1 == 2 (normally false, but provable from false)
        collect_obligation(
            ObligationKind::Assert,
            "one_equals_two".to_string(),
            "1 == 2".to_string(),
            Some("test:2:1".to_string()),
        );

        let result = verify_collected();

        // Vacuous truth detection (#2258): requires(false) makes assumptions
        // contradictory, which is now caught and reported as Unknown.
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "requires(false) should be caught by vacuous truth check, got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_does_not_need_proof() {
    // Requires conditions are NOT verified - they're assumed
    common::with_clean_verification(|| {
        // Requires: 1 == 2 (false, but we assume it)
        collect_obligation(
            ObligationKind::Requires,
            "impossible_req".to_string(),
            "1 == 2".to_string(),
            Some("test:1:1".to_string()),
        );

        // Assert: 2 == 1 (follows from the assumption)
        collect_obligation(
            ObligationKind::Assert,
            "reversed".to_string(),
            "2 == 1".to_string(),
            Some("test:2:1".to_string()),
        );

        let result = verify_collected();

        // Vacuous truth detection (#2258): requires(1 == 2) is false,
        // making assumptions contradictory → caught as Unknown.
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "requires(1 == 2) should be caught by vacuous truth check, got: {:?}",
            result
        );
    })
}

#[test]
fn test_multiple_requires_are_conjunctive() {
    // Multiple requires are ANDed together.
    // Variables bounded to prevent BV32 overflow in x + y.
    common::with_clean_verification(|| {
        collect_variable("x".to_string(), "i32".to_string());
        collect_variable("y".to_string(), "i32".to_string());

        // Requires: x > 0 && x < 1000 (bounded to prevent BV overflow)
        collect_obligation(
            ObligationKind::Requires,
            "x_pos".to_string(),
            "x > 0 && x < 1000".to_string(),
            Some("test:1:1".to_string()),
        );

        // Requires: y > 0 && y < 1000 (bounded to prevent BV overflow)
        collect_obligation(
            ObligationKind::Requires,
            "y_pos".to_string(),
            "y > 0 && y < 1000".to_string(),
            Some("test:2:1".to_string()),
        );

        // Assert: x + y > 0 (safe: max x+y = 999+999 = 1998, fits in i32)
        collect_obligation(
            ObligationKind::Assert,
            "sum_pos".to_string(),
            "x + y > 0".to_string(),
            Some("test:3:1".to_string()),
        );

        let result = verify_collected();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Given requires(x > 0 && x < 1000) && requires(y > 0 && y < 1000), assert(x + y > 0) should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_ensures_is_assertion_not_assumption() {
    // Ensures is an assertion (postcondition) that needs proof
    common::with_clean_verification(|| {
        // Ensures: false (should fail - can't prove false)
        collect_obligation(
            ObligationKind::Ensures,
            "impossible_ensures".to_string(),
            "false".to_string(),
            Some("test:1:1".to_string()),
        );

        let result = verify_collected();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "ensures(false) should produce counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_implication_semantics() {
    // Function verification is proving: requires => ensures
    common::with_clean_verification(|| {
        collect_variable("n".to_string(), "i32".to_string());

        // Requires: n >= 0 && n < 1000 (bounded to prevent BV32 overflow in n + 1)
        collect_obligation(
            ObligationKind::Requires,
            "n_nonneg".to_string(),
            "n >= 0 && n < 1000".to_string(),
            Some("test:1:1".to_string()),
        );

        // Ensures: n + 1 > 0 (provable given 0 <= n < 1000, no overflow)
        collect_obligation(
            ObligationKind::Ensures,
            "result_pos".to_string(),
            "n + 1 > 0".to_string(),
            Some("test:2:1".to_string()),
        );

        let result = verify_collected();

        assert!(
            matches!(result, VerifyResult::Verified),
            "requires(n >= 0 && n < 1000) => ensures(n + 1 > 0) should verify, got: {:?}",
            result
        );
    })
}
