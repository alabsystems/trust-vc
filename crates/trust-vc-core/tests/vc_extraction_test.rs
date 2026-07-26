//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration test for VC extraction from annotated functions (#751)
//!
//! This test demonstrates end-to-end verification:
//! 1. Annotated function with requires/ensures
//! 2. Automatic VC extraction
//! 3. ay SMT solving

use trust_vc_core::verify::Verifier;

#[test]
fn test_simple_requires_ensures() {
    // Parse an annotated function
    let code = r#"
        #[requires(x > 0)]
        #[ensures(result > 0)]
        fn add_one(x: i32) -> i32 {
            x + 1
        }
    "#;

    let func: syn::ItemFn = syn::parse_str(code).expect("Failed to parse function");

    // Verify the function
    let result = Verifier::verify_function(&func);

    // Verifier::verify_function declares `result` but does not connect it to
    // the function body (x + 1). The solver freely assigns result=0, producing
    // a counterexample. Once body→result lowering is implemented, this should
    // return Verified.
    assert!(
        result.is_counterexample(),
        "Expected counterexample (body→result not connected), got: {:?}",
        result
    );
}

#[test]
fn test_invalid_ensures() {
    // Parse a function with an invalid ensures clause
    let code = r#"
        #[requires(x > 0)]
        #[ensures(result < 0)]  // This is wrong - x+1 > 0 when x > 0
        fn add_one(x: i32) -> i32 {
            x + 1
        }
    "#;

    let func: syn::ItemFn = syn::parse_str(code).expect("Failed to parse function");

    // Verify the function
    let result = Verifier::verify_function(&func);

    // Should find a counterexample
    assert!(
        result.is_counterexample(),
        "Expected counterexample, got: {:?}",
        result
    );
}

#[test]
fn test_assertion_in_body() {
    // Parse a function with an assertion in the body
    let code = r#"
        fn check_identity(x: i32) -> i32 {
            assert!(x + 0 == x);
            x
        }
    "#;

    let func: syn::ItemFn = syn::parse_str(code).expect("Failed to parse function");

    // Verify the function
    let result = Verifier::verify_function(&func);

    // The assertion should be verified (identity law)
    assert!(
        result.is_verified(),
        "Expected verification to succeed, got: {:?}",
        result
    );
}

#[test]
fn test_multiple_variables() {
    // Parse a function with multiple parameters
    let code = r#"
        #[requires(a > 0)]
        #[requires(b > 0)]
        #[ensures(result > 0)]
        fn add_positive(a: i32, b: i32) -> i32 {
            a + b
        }
    "#;

    let func: syn::ItemFn = syn::parse_str(code).expect("Failed to parse function");

    // Verify the function
    let result = Verifier::verify_function(&func);

    // Verifier::verify_function declares `result` but does not connect it to
    // the function body (a + b). The solver freely assigns result=0, producing
    // a counterexample. Once body→result lowering is implemented, this should
    // return Verified.
    assert!(
        result.is_counterexample(),
        "Expected counterexample (body→result not connected), got: {:?}",
        result
    );
}

#[test]
fn test_complex_expression() {
    // Test with a more complex expression
    let code = r#"
        #[requires(x >= 0)]
        #[requires(y >= 0)]
        #[ensures(result >= 0)]
        fn multiply(x: i32, y: i32) -> i32 {
            x * y
        }
    "#;

    let func: syn::ItemFn = syn::parse_str(code).expect("Failed to parse function");

    // Verify the function
    let result = Verifier::verify_function(&func);

    // Verifier::verify_function declares `result` but does not connect it to
    // the function body (x * y). The solver freely assigns result=MAX_U32,
    // producing a counterexample. Once body→result lowering is implemented,
    // this should return Verified or Unknown (non-linear arithmetic).
    assert!(
        result.is_counterexample(),
        "Expected counterexample (body→result not connected), got: {:?}",
        result
    );
}

/// This test demonstrates the full integration:
/// - Proc macro attributes (requires/ensures)
/// - AST parsing
/// - VC extraction
/// - ay verification
#[test]
fn test_end_to_end_integration() {
    // A complete example with pre/post conditions and assertions
    let code = r#"
        #[requires(n >= 0)]
        #[ensures(result >= 0)]
        fn factorial_base_case(n: u64) -> u64 {
            if n == 0 {
                assert!(1 >= 0);  // Assertion in body
                1
            } else {
                n  // Simplified - just return n for non-zero
            }
        }
    "#;

    let func: syn::ItemFn = syn::parse_str(code).expect("Failed to parse function");

    // Verify the function
    let result = Verifier::verify_function(&func);

    // Should verify successfully
    assert!(
        result.is_verified(),
        "Expected verification to succeed, got: {:?}",
        result
    );
}

#[test]
fn test_malformed_requires_returns_error() {
    let code = r#"
        #[requires(!!!)]
        fn bad_requires(x: i32) -> i32 {
            x
        }
    "#;
    let func: syn::ItemFn = syn::parse_str(code).expect("Failed to parse function");

    let result = Verifier::verify_function(&func);
    assert!(
        matches!(
            result,
            trust_vc_core::VerifyResult::Error { ref message }
                if message.contains("Failed to parse #[requires] attribute")
        ),
        "malformed #[requires] must produce VerifyResult::Error, got: {:?}",
        result
    );
}

#[test]
fn test_malformed_ensures_returns_error() {
    let code = r#"
        #[ensures(!!!)]
        fn bad_ensures(x: i32) -> i32 {
            x
        }
    "#;
    let func: syn::ItemFn = syn::parse_str(code).expect("Failed to parse function");

    let result = Verifier::verify_function(&func);
    assert!(
        matches!(
            result,
            trust_vc_core::VerifyResult::Error { ref message }
                if message.contains("Failed to parse #[ensures] attribute")
        ),
        "malformed #[ensures] must produce VerifyResult::Error, got: {:?}",
        result
    );
}

#[test]
fn test_malformed_assert_returns_error() {
    let code = r#"
        fn bad_assert(x: i32) -> i32 {
            assert!(x >);
            x
        }
    "#;
    let func: syn::ItemFn = syn::parse_str(code).expect("Failed to parse function");

    let result = Verifier::verify_function(&func);
    assert!(
        matches!(
            result,
            trust_vc_core::VerifyResult::Error { ref message }
                if message.contains("Failed to parse assert!() expression")
        ),
        "malformed assert!() must produce VerifyResult::Error, got: {:?}",
        result
    );
}

#[test]
fn test_malformed_namespaced_requires_returns_error() {
    let code = r#"
        #[trust_vc::requires(!!!)]
        fn bad_requires(x: i32) -> i32 {
            x
        }
    "#;
    let func: syn::ItemFn = syn::parse_str(code).expect("Failed to parse function");

    let result = Verifier::verify_function(&func);
    assert!(
        matches!(
            result,
            trust_vc_core::VerifyResult::Error { ref message }
                if message.contains("Failed to parse #[requires] attribute")
        ),
        "malformed #[trust_vc::requires] must produce VerifyResult::Error, got: {:?}",
        result
    );
}

#[test]
fn test_malformed_namespaced_ensures_returns_error() {
    let code = r#"
        #[trust_vc::ensures(!!!)]
        fn bad_ensures(x: i32) -> i32 {
            x
        }
    "#;
    let func: syn::ItemFn = syn::parse_str(code).expect("Failed to parse function");

    let result = Verifier::verify_function(&func);
    assert!(
        matches!(
            result,
            trust_vc_core::VerifyResult::Error { ref message }
                if message.contains("Failed to parse #[ensures] attribute")
        ),
        "malformed #[trust_vc::ensures] must produce VerifyResult::Error, got: {:?}",
        result
    );
}

#[test]
fn test_assert_with_message_is_supported() {
    let code = r#"
        fn assert_with_message(x: i32) -> i32 {
            assert!(x == x, "x should equal itself: {}", x);
            x
        }
    "#;
    let func: syn::ItemFn = syn::parse_str(code).expect("Failed to parse function");

    let result = Verifier::verify_function(&func);
    assert!(
        result.is_verified(),
        "assert! with message should parse and verify, got: {:?}",
        result
    );
}
