// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for automatic VC extraction from annotated Rust functions.

use syn::{parse_str, ItemFn};
use trust_vc_core::extract_verification_conditions;
use trust_vc_core::VerifyResult;

#[test]
fn test_extract_simple_identity() {
    let code = r#"
        #[requires(x >= 0)]
        #[ensures(result == x)]
        fn identity(x: i32) -> i32 {
            x
        }
    "#;

    let func = parse_str::<ItemFn>(code).unwrap();
    let vc = extract_verification_conditions(&func).unwrap();

    // Should have two variables: parameter x and implicit result
    assert_eq!(vc.variables().len(), 2);
    assert_eq!(vc.variables()[0].name, "x");
    assert_eq!(vc.variables()[1].name, "result");

    // Should have three obligations: requires (assume), ensures (assert),
    // and return_value assumption connecting body to result
    assert_eq!(vc.obligations().len(), 3);

    // First should be the assumption (requires)
    let first_obligation = vc
        .obligations()
        .first()
        .expect("Should have first obligation after length check");
    assert_eq!(first_obligation.condition(), "x >= 0");
    assert!(matches!(
        first_obligation.kind(),
        trust_vc_core::vc::ObligationKind::Assume
    ));

    // Second should be the assertion (ensures)
    let second_obligation = vc
        .obligations()
        .get(1)
        .expect("Should have second obligation after length check");
    assert_eq!(second_obligation.condition(), "result == x");
    assert!(matches!(
        second_obligation.kind(),
        trust_vc_core::vc::ObligationKind::Assert
    ));

    // Third is the return_value assumption (result == body return expr)
    let third_obligation = vc
        .obligations()
        .get(2)
        .expect("Should have third obligation after length check");
    assert_eq!(third_obligation.condition(), "result == x");
    assert!(matches!(
        third_obligation.kind(),
        trust_vc_core::vc::ObligationKind::Assume
    ));

    // Should verify successfully
    let result = vc.verify();
    assert!(matches!(result, VerifyResult::Verified));
}

#[test]
fn test_extract_increment() {
    let code = r#"
        #[requires(x < 2147483647)]
        #[ensures(result > x)]
        fn increment(x: i32) -> i32 {
            x + 1
        }
    "#;

    let func = parse_str::<ItemFn>(code).unwrap();
    let vc = extract_verification_conditions(&func).unwrap();

    // Should have two variables: parameter x and implicit result
    assert_eq!(vc.variables().len(), 2);
    assert_eq!(vc.variables()[0].name, "x");
    assert_eq!(vc.variables()[1].name, "result");

    // Three obligations: requires, ensures, return_value assumption
    assert_eq!(vc.obligations().len(), 3);
    assert_eq!(
        vc.obligations()
            .first()
            .expect("Should have first obligation after length check")
            .condition(),
        "x < 2147483647"
    );
    assert_eq!(
        vc.obligations()
            .get(1)
            .expect("Should have second obligation after length check")
            .condition(),
        "result > x"
    );
    assert_eq!(
        vc.obligations()
            .get(2)
            .expect("Should have return_value obligation")
            .condition(),
        "result == x + 1"
    );

    // Body-to-result connection via return_value assumption means this now
    // verifies on the stable BV path:
    // x < i32::MAX ∧ result == x+1 -> result > x
    let result = vc.verify();
    assert!(matches!(result, VerifyResult::Verified));
}

#[test]
fn test_extract_with_body_assertion() {
    let code = r#"
        fn test_assertion(x: i32) {
            trust_vc_assert!(x + 0 == x);
        }
    "#;

    let func = parse_str::<ItemFn>(code).unwrap();
    let vc = extract_verification_conditions(&func).unwrap();

    // Should have one variable
    assert_eq!(vc.variables().len(), 1);
    assert_eq!(vc.variables()[0].name, "x");

    // Should have one assertion from the body
    assert!(!vc.obligations().is_empty());
    assert!(vc
        .obligations()
        .first()
        .expect("Should have first obligation after non-empty check")
        .condition()
        .contains("x + 0 == x"));

    // Should verify successfully
    let result = vc.verify();
    assert!(matches!(result, VerifyResult::Verified));
}

#[test]
fn test_integration_with_actual_verification() {
    // This tests the actual end-to-end flow (body connected to result).
    //
    // The precondition must bound `n` so that `n + n` cannot overflow `i32`:
    // exec-mode arithmetic-overflow checks are on by default, so the bare
    // `n > 0` form correctly fails closed with a `n = i32::MAX` multiplication
    // counterexample (the postcondition `result == n * 2` is genuinely false
    // for large `n`). Bounding `n` makes `double` actually correct, which is
    // what this end-to-end smoke test means to exercise.
    let code = r#"
        #[requires(n > 0 && n <= 1073741823)]
        #[ensures(result == n * 2)]
        fn double(n: i32) -> i32 {
            n + n
        }
    "#;

    let func = parse_str::<ItemFn>(code).unwrap();
    let vc = extract_verification_conditions(&func).unwrap();

    // Verify the extracted conditions
    assert_eq!(
        vc.variables()
            .first()
            .expect("Should have first variable")
            .name,
        "n"
    );
    assert_eq!(
        vc.obligations()
            .first()
            .expect("Should have first obligation")
            .condition(),
        "n > 0 && n <= 1073741823"
    );
    assert_eq!(
        vc.obligations()
            .get(1)
            .expect("Should have second obligation")
            .condition(),
        "result == n * 2"
    );

    // Verify the function - should pass now that body is connected to result
    // and `n` is bounded away from the i32 overflow boundary.
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Expected verification to pass, got: {:?}",
        result
    );
}

#[test]
fn test_missing_return_expression_edge_case() {
    // Functions with return type but no detectable return expression should fail-closed
    // with an error (not silently leave `result` unconstrained). Fixed in #2251.
    let code = r#"
        #[ensures(result > 0)]
        fn always_positive() -> i32 {
            // No return expression - just a statement with semicolon
            let x = 42;
            x; // Note the semicolon makes this NOT a return expression
        }
    "#;

    let func = parse_str::<ItemFn>(code).unwrap();
    let result = extract_verification_conditions(&func);

    assert!(
        result.is_err(),
        "Expected Err for missing return expression, got: {:?}",
        result
    );
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("no detectable return expression"),
        "Error should mention missing return expression, got: {}",
        err_msg
    );
}

#[test]
fn test_macro_path_checking_issue() {
    // This test demonstrates that the current implementation doesn't properly
    // check macro paths - it only looks for identifier "assert" or "trust_vc_assert"
    let code = r#"
        fn example() {
            // Using trust_vc_assert! identifier (what the code looks for)
            trust_vc_assert!(true);
        }
    "#;

    let func = parse_str::<ItemFn>(code).unwrap();
    let vc = extract_verification_conditions(&func).unwrap();

    // The current implementation looks for "trust_vc_assert" as an identifier
    // This test documents what actually works vs what should work
    assert_eq!(
        vc.obligations().len(),
        1,
        "Should extract trust_vc_assert! macro"
    );

    // Note: trust_vc::assert! won't work with current implementation (issue #841)
}
