// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Improved test helpers for verification tests (#778).
//!
//! These helpers provide specific functions for each expected outcome,
//! making it clear what each test expects and failing appropriately
//! when the wrong outcome occurs.
//!
//! # Migration Guide
//!
//! If you're migrating from the old test_verify_helpers.rs:
//! - Replace `verify_should_pass()` with `expect_verified()`
//! - Replace `verify_should_fail()` with `expect_counterexample()`
//! - Replace direct `verify_collected()` calls with appropriate expect_* helper
//! - Always call `clear_context()` at the start of each test
//!
//! # When to Use Each Helper
//!
//! - `expect_verified()`: When you expect all assertions to pass
//! - `expect_counterexample()`: When you expect verification to find a counterexample
//! - `expect_unknown()`: When testing solver limitations or timeouts
//! - `expect_error()`: When testing error handling in the verification pipeline
//! - `expect_verified_or_unknown()`: For non-deterministic tests (e.g., solver timeouts)

use trust_vc_core::VerifyResult;

/// Helper that only accepts Verified outcome
///
/// Use this when you expect all verification conditions to pass.
/// This replaces the old `verify_should_pass()` helper.
///
/// # Example
/// ```no_run
/// use test_verify_helpers_v2::*;
///
/// fn test_simple_assertion() {
///     clear_context();
///     trust_vc::assert!(5 > 3);
///     trust_vc::assert!(10 == 10);
///     expect_verified().expect("Both assertions should verify");
/// }
/// ```
///
/// # Migration from Old Helper
/// ```
/// // Old way:
/// verify_should_pass().expect("Should pass");
///
/// // New way:
/// expect_verified().expect("Should verify");
/// ```
#[allow(dead_code)]
pub fn expect_verified() -> Result<(), String> {
    // NOW USING THE BRIDGE: Connect proc macros to ay verification
    let pipeline = trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
    let result = pipeline.verify();
    match result {
        VerifyResult::Verified => Ok(()),
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => Err(format!(
            "Expected Verified but got Counterexample for '{}' with model: {:?}",
            obligation_name, model
        )),
        VerifyResult::Unknown { reason, .. } => {
            Err(format!("Expected Verified but got Unknown: {}", reason))
        }
        VerifyResult::Error { message } => {
            Err(format!("Expected Verified but got Error: {}", message))
        }
        other => Err(format!(
            "Expected Verified but got unexpected result: {:?}",
            other
        )),
    }
}

/// Helper that only accepts Counterexample outcome
///
/// Use this when you expect verification to find a counterexample (i.e., the assertion should fail).
/// This replaces the old `verify_should_fail()` helper and is more precise about what kind of failure is expected.
///
/// # Example
/// ```
/// use test_verify_helpers_v2::*;
///
/// // Test function
/// fn test_invalid_assertion() {
///     clear_context();
///     trust_vc::assert!(3 > 5);  // This is false, should fail
///     let (obligation_name, model) = expect_counterexample()
///         .expect("Should find counterexample for false assertion");
///     assert!(obligation_name.contains("assert"));
/// }
/// ```
///
/// # Migration from Old Helper
/// ```
/// // Old way:
/// verify_should_fail().expect("Should fail");
///
/// // New way:
/// let (obligation, model) = expect_counterexample().expect("Should find counterexample");
/// // Now you can also inspect which obligation failed and what the counterexample was
/// ```
#[allow(dead_code)]
pub fn expect_counterexample() -> Result<(String, Option<String>), String> {
    // NOW USING THE BRIDGE: Connect proc macros to ay verification
    let pipeline = trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
    let result = pipeline.verify();
    match result {
        VerifyResult::Verified => Err("Expected Counterexample but got Verified".to_string()),
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => Ok((obligation_name, model)),
        VerifyResult::Unknown { reason, .. } => Err(format!(
            "Expected Counterexample but got Unknown: {}",
            reason
        )),
        VerifyResult::Error { message } => Err(format!(
            "Expected Counterexample but got Error: {}",
            message
        )),
        other => Err(format!(
            "Expected Counterexample but got unexpected result: {:?}",
            other
        )),
    }
}

/// Helper that only accepts Unknown outcome
///
/// Use this when testing solver limitations, timeouts, or undecidable conditions.
/// Unknown results typically occur when the SMT solver cannot determine satisfiability
/// within resource limits.
///
/// # Example
/// ```
/// use test_verify_helpers_v2::*;
///
/// // Test function
/// fn test_complex_quantifier() {
///     clear_context();
///     // Complex nested quantifiers might cause Unknown result
///     trust_vc::assert!(forall(|x: i32| exists(|y: i32| x + y == 0)));
///     let reason = expect_unknown().expect("Complex quantifiers may be undecidable");
///     assert!(reason.contains("timeout") || reason.contains("undecidable"));
/// }
/// ```
#[allow(dead_code)]
pub fn expect_unknown() -> Result<String, String> {
    // NOW USING THE BRIDGE: Connect proc macros to ay verification
    let pipeline = trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
    let result = pipeline.verify();
    match result {
        VerifyResult::Verified => Err("Expected Unknown but got Verified".to_string()),
        VerifyResult::Counterexample {
            obligation_name, ..
        } => Err(format!(
            "Expected Unknown but got Counterexample for '{}'",
            obligation_name
        )),
        VerifyResult::Unknown { reason, .. } => Ok(reason),
        VerifyResult::Error { message } => {
            Err(format!("Expected Unknown but got Error: {}", message))
        }
        other => Err(format!(
            "Expected Unknown but got unexpected result: {:?}",
            other
        )),
    }
}

/// Helper that only accepts Error outcome
///
/// Use this when testing error conditions in the verification pipeline itself,
/// such as malformed SMT queries or context errors.
///
/// # Example
/// ```
/// use test_verify_helpers_v2::*;
///
/// // Test function
/// fn test_malformed_context() {
///     // Don't clear context, try to verify with empty context
///     // This should produce an error
///     let error_msg = expect_error().expect("Empty context should produce error");
///     assert!(error_msg.contains("no obligations") || error_msg.contains("empty"));
/// }
/// ```
#[allow(dead_code)]
pub fn expect_error() -> Result<String, String> {
    // NOW USING THE BRIDGE: Connect proc macros to ay verification
    let pipeline = trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
    let result = pipeline.verify();
    match result {
        VerifyResult::Verified => Err("Expected Error but got Verified".to_string()),
        VerifyResult::Counterexample {
            obligation_name, ..
        } => Err(format!(
            "Expected Error but got Counterexample for '{}'",
            obligation_name
        )),
        VerifyResult::Unknown { reason, .. } => {
            Err(format!("Expected Error but got Unknown: {}", reason))
        }
        VerifyResult::Error { message } => Ok(message),
        other => Err(format!(
            "Expected Error but got unexpected result: {:?}",
            other
        )),
    }
}

/// Helper that accepts either Verified or Unknown (for solver timeout tests)
///
/// Use this for non-deterministic tests where the solver might timeout on complex problems
/// but still shouldn't produce counterexamples.
///
/// # Example
/// ```
/// use test_verify_helpers_v2::*;
///
/// // Test function
/// fn test_possibly_timeout() {
///     clear_context();
///     // Very complex assertion that might timeout
///     trust_vc::assert!(complex_property_with_many_quantifiers());
///     match expect_verified_or_unknown().expect("Should either verify or timeout") {
///         VerifyResult::Verified => println!("Verified successfully"),
///         VerifyResult::Unknown { reason, .. } => println!("Timed out: {}", reason),
///         _ => unreachable!(),
///     }
/// }
/// ```
#[allow(dead_code)]
pub fn expect_verified_or_unknown() -> Result<VerifyResult, String> {
    // NOW USING THE BRIDGE: Connect proc macros to ay verification
    let pipeline = trust_vc_core::verification_bridge::VerificationPipeline::collect_from_macros();
    let result = pipeline.verify();
    match result {
        VerifyResult::Verified | VerifyResult::Unknown { .. } => Ok(result),
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => Err(format!(
            "Expected Verified/Unknown but got Counterexample for '{}' with model: {:?}",
            obligation_name, model
        )),
        VerifyResult::Error { message } => Err(format!(
            "Expected Verified/Unknown but got Error: {}",
            message
        )),
        other => Err(format!(
            "Expected Verified/Unknown but got unexpected result: {:?}",
            other
        )),
    }
}

/// Clear verification state for a fresh sub-test
///
/// **IMPORTANT**: Prefer using `common::with_clean_verification()` instead.
/// This function clears the verification context, registrations, and extern
/// contracts. It preserves proof mode state that proc macros may depend on.
/// Without cleanup, obligations from previous tests may contaminate your test.
///
/// # Example
/// ```
/// use test_verify_helpers_v2::*;
///
/// // Test function
/// fn my_test() {
///     clear_context();  // Clears verification state
///     // Now add your assertions...
///     trust_vc::assert!(true);
///     expect_verified().expect("Should verify");
/// }
/// ```
#[allow(dead_code)]
pub fn clear_context() {
    trust_vc_core::verify_macro::clear_context();
    trust_vc_core::verification_bridge::clear_registrations();
    trust_vc_core::clear_extern_contracts();
}

/// Check if we have any obligations collected
///
/// Useful for debugging when verification unexpectedly passes (might mean no obligations were collected).
///
/// # Example
/// ```
/// use test_verify_helpers_v2::*;
///
/// // Test function
/// fn test_obligations_collected() {
///     clear_context();
///     trust_vc::assert!(5 > 3);
///     assert!(has_obligations(), "Should have collected at least one obligation");
///     expect_verified().expect("Should verify");
/// }
/// ```
#[allow(dead_code)]
pub fn has_obligations() -> bool {
    if let Some(context) = trust_vc_core::verify_macro::get_context() {
        !context.obligations().is_empty()
    } else {
        false
    }
}

/// Get the number of obligations collected
///
/// Useful for ensuring the expected number of assertions were collected.
///
/// # Example
/// ```
/// use test_verify_helpers_v2::*;
///
/// // Test function
/// fn test_multiple_assertions() {
///     clear_context();
///     trust_vc::assert!(1 > 0);
///     trust_vc::assert!(2 > 1);
///     trust_vc::assert!(3 > 2);
///     assert_eq!(obligation_count(), 3, "Should have collected 3 obligations");
///     expect_verified().expect("All should verify");
/// }
/// ```
#[allow(dead_code)]
pub fn obligation_count() -> usize {
    if let Some(context) = trust_vc_core::verify_macro::get_context() {
        context.obligations().len()
    } else {
        0
    }
}
