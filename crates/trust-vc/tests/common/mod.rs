// Common test helpers for proper verification testing
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Standard test helpers that ensure tests actually run verification.
//! All tests should use these helpers instead of raw macro calls.

#![allow(dead_code)]
#![allow(clippy::test_attr_in_doctest)]

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

pub fn pinned_verus_test_path(relative_under_tests: &str) -> std::path::PathBuf {
    let root = std::env::var_os("VERUS_ROOT")
        .or_else(|| std::env::var_os("TRUST_VC_VERUS_ROOT"))
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../..")
                .join("verus")
        });

    root.join("source/rust_verify_test/tests")
        .join(relative_under_tests)
}

fn extract_panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else if let Some(s) = payload.downcast_ref::<&str>() {
        s.to_string()
    } else {
        "unknown panic".to_string()
    }
}

fn panic_message_to_verify_result(msg: String) -> Option<VerifyResult> {
    if msg.contains("Proof verification failed")
        || msg.contains("Counterexample")
        || msg.contains("trust_vc precondition failed")
        || msg.contains("trust_vc postcondition failed")
        || msg.contains("trust_vc assertion failed")
    {
        Some(VerifyResult::Counterexample {
            obligation_name: "caught_verification_failure".to_string(),
            location: None,
            model: Some(msg),
            bindings: Vec::new(),
        })
    } else if msg.contains("Proof verification returned Unknown") {
        Some(VerifyResult::Unknown {
            category: trust_vc_core::UnknownCategory::classify(&msg),
            reason: msg,
        })
    } else if msg.contains("Proof verification error")
        || msg.contains("Proof verification returned unexpected result")
    {
        Some(VerifyResult::Error { message: msg })
    } else if msg.contains("INVALID:") {
        Some(VerifyResult::Counterexample {
            obligation_name: "caught_validation_failure".to_string(),
            location: None,
            model: Some(msg),
            bindings: Vec::new(),
        })
    } else {
        None
    }
}

/// Verify a `VerificationContext` through the standard `VerificationPipeline`.
///
/// Use this for direct-context tests (e.g., VerifyThis algorithm suites) that
/// build a `VerificationContext` by hand instead of using proc macros.
/// Part of #1918.
pub fn verify_context_with_pipeline(context: VerificationContext) -> VerifyResult {
    let mut pipeline = VerificationPipeline::new();
    pipeline.replace_context(context);
    pipeline.verify()
}

/// Clears all thread-local verification state.
fn clear_all_state() {
    verify_macro::clear_all_thread_locals();
    trust_vc_core::verification_bridge::clear_registrations();
    trust_vc_core::clear_extern_contracts();
}

/// Runs a test function with clean verification state.
///
/// This helper ensures all thread-local storage is cleared before and after
/// the test, preventing memory leaks and cross-test contamination.
/// Uses catch_unwind to guarantee cleanup even if the closure panics.
pub fn with_clean_verification<F, R>(f: F) -> R
where
    F: FnOnce() -> R,
{
    // Clear any pre-existing state from previous tests
    clear_all_state();

    // Run the test with panic safety — cleanup must happen even on panic
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));

    // Always clean up, even on panic (fixes #1532)
    clear_all_state();

    match result {
        Ok(value) => value,
        Err(panic_payload) => std::panic::resume_unwind(panic_payload),
    }
}

/// Run a proof function and verify it should pass.
///
/// Handles two calling patterns:
/// 1. **`#[proof]` functions**: Auto-verify internally and panic on failure.
///    After returning, VERIFICATION_CONTEXT is empty (restored by ContextGuard).
/// 2. **Raw obligation closures** (using `assert_by!`, `trust_vc::assert!` without `#[proof]`):
///    Obligations accumulate in VERIFICATION_CONTEXT and need external verification.
///
/// After the closure runs, we check if obligations remain in the context.
/// If yes, we verify them externally. If no (already consumed by auto-verify),
/// the proof already succeeded internally.
/// Uses comprehensive cleanup (fixes #1531).
#[track_caller]
pub fn verify_should_pass<F>(proof_fn: F) -> VerifyResult
where
    F: FnOnce(),
{
    let caller = std::panic::Location::caller();
    with_clean_verification(|| {
        // Snapshot monotonic counter before running — survives context clears (#1713)
        let before = verify_macro::total_obligations_collected();

        // Execute the proof/closure - may auto-verify internally (#[proof])
        // or just collect obligations (assert_by!, raw trust_vc::assert!)
        proof_fn();

        // Check if there are uncollected obligations remaining
        let pipeline = VerificationPipeline::collect_from_macros();
        if pipeline.context().obligations().is_empty() {
            let after = verify_macro::total_obligations_collected();
            if after == before {
                // No obligations were EVER collected — silent vacuous pass (#1713)
                panic!(
                    "[{}] verify_should_pass: closure collected zero obligations. \
                     This is a silent vacuous pass — the proof function generated \
                     nothing to verify. Check macro expansion or obligation collection.",
                    caller
                );
            }
            // Obligations were collected and auto-verified (e.g., #[proof])
            VerifyResult::Verified
        } else {
            // Obligations present but not yet verified - verify them now
            let result = pipeline.verify();
            match &result {
                VerifyResult::Verified => {}
                VerifyResult::Counterexample {
                    obligation_name,
                    model,
                    ..
                } => {
                    panic!(
                        "[{}] Proof should verify but got counterexample.\nObligation: {}\nModel: {}",
                        caller,
                        obligation_name,
                        model.as_deref().unwrap_or("no model")
                    );
                }
                VerifyResult::Unknown { reason, .. } => {
                    panic!(
                        "[{}] Proof should verify but solver returned unknown.\nReason: {}",
                        caller, reason
                    );
                }
                VerifyResult::Error { message } => {
                    panic!(
                        "[{}] Proof should verify but got error.\nError: {}",
                        caller, message
                    );
                }
                other => {
                    panic!(
                        "[{}] Proof should verify but got unexpected result: {:?}",
                        caller, other
                    );
                }
            }
            result
        }
    })
}

/// Run a proof function and verify it should fail.
///
/// Handles two calling patterns:
/// 1. **`#[proof]` functions**: Auto-verify internally and panic on failure.
///    We catch the panic to confirm the proof was rejected.
/// 2. **Raw obligation closures** (using `assert_by!`, `trust_vc::assert!` without `#[proof]`):
///    Obligations accumulate and we verify externally, expecting failure.
///
/// Uses comprehensive cleanup (fixes #1531).
#[track_caller]
pub fn verify_should_fail<F>(proof_fn: F) -> VerifyResult
where
    F: FnOnce(),
{
    let caller = std::panic::Location::caller();
    with_clean_verification(|| {
        // Try running the closure - #[proof] functions may panic on failure
        let run_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(proof_fn));

        match run_result {
            Err(payload) => {
                let msg = extract_panic_message(payload.as_ref());
                if let Some(result) = panic_message_to_verify_result(msg.clone()) {
                    result
                } else {
                    // Non-verification panic (index OOB, unwrap on None, ay internal
                    // error, invariant violation, etc.) — infrastructure bug, not a
                    // proof rejection. "invariant:" panics are programmer errors in
                    // the framework, not user-facing failures.
                    panic!(
                        "[{}] Proof function panicked with non-verification error \
                         (infrastructure bug, not a proof rejection):\n  {}",
                        caller, msg
                    );
                }
            }
            Ok(()) => {
                // Closure succeeded without panic - check for uncollected obligations
                let pipeline = VerificationPipeline::collect_from_macros();
                if pipeline.context().obligations().is_empty() {
                    // No obligations and no panic - proof passed (unexpected)
                    panic!("[{}] Proof should NOT verify but it succeeded", caller);
                }
                // Obligations present - verify them, expecting failure
                let result = pipeline.verify();
                assert!(
                    !matches!(result, VerifyResult::Verified),
                    "[{}] Proof should NOT verify but got Verified",
                    caller
                );
                result
            }
        }
    })
}

/// Run a proof and return the raw result without assertions.
///
/// Handles both `#[proof]` auto-verify (catches panics) and raw obligation
/// collection (verifies remaining obligations externally).
/// Uses comprehensive cleanup (fixes #1531).
#[track_caller]
pub fn verify_and_get_result<F>(proof_fn: F) -> VerifyResult
where
    F: FnOnce(),
{
    with_clean_verification(|| {
        let before = verify_macro::total_obligations_collected();
        let run_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(proof_fn));
        match run_result {
            Ok(()) => {
                // Closure succeeded - check for uncollected obligations
                let pipeline = VerificationPipeline::collect_from_macros();
                if pipeline.context().obligations().is_empty() {
                    let after = verify_macro::total_obligations_collected();
                    if after == before {
                        // No obligations ever collected — vacuous pass (#1713)
                        return VerifyResult::Error {
                            message: "Zero obligations collected — vacuous pass".to_string(),
                        };
                    }
                    // #[proof] auto-verified
                    VerifyResult::Verified
                } else {
                    // Raw obligations need external verification
                    pipeline.verify()
                }
            }
            Err(payload) => {
                let msg = extract_panic_message(payload.as_ref());
                panic_message_to_verify_result(msg.clone())
                    .unwrap_or(VerifyResult::Error { message: msg })
            }
        }
    })
}

/// Check that a proof produces a specific verification result
#[track_caller]
pub fn verify_with_expected<F>(proof_fn: F, expected: VerifyResult)
where
    F: FnOnce(),
{
    let caller = std::panic::Location::caller();
    let result = verify_and_get_result(proof_fn);
    assert_eq!(
        result, expected,
        "[{}] Expected {:?} but got {:?}",
        caller, expected, result
    );
}

/// Legacy compatibility wrapper for proc-macro verification tests.
///
/// Prefer the named outcome helpers in `test_verify_helpers_v2.rs` for new
/// proc-macro tests:
///
/// ```text
/// clear_context();
///
/// #[trust_vc::proof]
/// fn valid_proof() {
///     trust_vc::assert!(true);
/// }
///
/// valid_proof();
/// expect_verified().expect("proof should verify");
/// ```
///
/// `VerificationTest`, `verify_should_pass`, and `verify_should_fail` remain
/// available for older tests that still use the legacy helper vocabulary.
pub struct VerificationTest;

impl VerificationTest {
    pub fn new() -> Self {
        clear_all_state();
        VerificationTest
    }

    pub fn run_and_verify_pass<F>(&self, proof_fn: F) -> VerifyResult
    where
        F: FnOnce(),
    {
        verify_should_pass(proof_fn)
    }

    pub fn run_and_verify_fail<F>(&self, proof_fn: F) -> VerifyResult
    where
        F: FnOnce(),
    {
        verify_should_fail(proof_fn)
    }
}
