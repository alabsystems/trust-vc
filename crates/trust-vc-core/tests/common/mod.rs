// Common test helpers for proper verification testing in trust-vc-core
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Standard test helpers that ensure tests actually run verification
//! and properly clean up thread-local storage to prevent memory leaks.

use trust_vc_core::verification_bridge::clear_registrations;
use trust_vc_core::verify_macro::clear_all_thread_locals;

/// Runs a test function with clean verification state.
///
/// This helper ensures all thread-local storage is cleared after the test,
/// preventing memory leaks from accumulated verification state.
///
/// # Example
/// ```no_run
/// fn test_my_feature() {
///     with_clean_verification(|| {
///         // Your test code here
///     });
/// }
/// ```
pub fn with_clean_verification<F, R>(f: F) -> R
where
    F: FnOnce() -> R,
{
    // Clear any pre-existing state
    clear_all_thread_locals();
    clear_registrations();
    trust_vc_core::clear_extern_contracts();

    // Run the test with panic safety — cleanup must happen even on panic (fixes #1532)
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));

    // Always clean up, even on panic
    clear_all_thread_locals();
    clear_registrations();
    trust_vc_core::clear_extern_contracts();

    match result {
        Ok(value) => value,
        Err(panic_payload) => std::panic::resume_unwind(panic_payload),
    }
}
