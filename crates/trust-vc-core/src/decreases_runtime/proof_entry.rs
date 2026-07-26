//! Proof-entry verification plumbing for decreases proofs.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from decreases_runtime.rs as part of #2010.
//! Contains recursive call decrease obligations and proof verification entry points.

use crate::error::TrustVcError;
use crate::obligation_collection::record_obligation_drop;
use crate::proof_session::try_with_session_mut;
use crate::vc::VerificationContext;
use crate::vc_extraction::try_verify_function_from_file;

/// Collects a decrease obligation for a recursive call.
///
/// This is called for each recursive call site to ensure the measure
/// decreases at that point, proving termination.
pub fn collect_decrease_obligation(call_site: &str, decrease_expr: &str, location: Option<&str>) {
    // Borrow conflicts must fail closed — otherwise termination checks can
    // disappear silently from the verification context. Part of #2360.
    match try_with_session_mut(|s| {
        let context = s.context.get_or_insert_with(VerificationContext::new);
        context.add_measure_decreases_obligation(
            &format!("decrease_check_{}", call_site),
            decrease_expr,
            location.map(|s| s.to_string()),
        );
    }) {
        Ok(()) => {}
        Err(_) => record_obligation_drop(),
    }
}

/// Verifies that recursive calls decrease the termination measure.
///
/// This is called after collecting the decreases measure to ensure
/// the function terminates.
pub fn verify_decreases(func_name: &str, entry_measure: String, recursive_call_measure: String) {
    // Borrow conflicts must fail closed — otherwise termination checks can
    // disappear silently from the verification context. Part of #2360.
    match try_with_session_mut(|s| {
        let context = s.context.get_or_insert_with(VerificationContext::new);
        context.add_measure_decreases(func_name, &entry_measure, &recursive_call_measure);
    }) {
        Ok(()) => {}
        Err(_) => record_obligation_drop(),
    }
}

/// Verifies a single proof function.
///
/// This is a more targeted version that verifies just one proof function
/// rather than all markers in a module.
///
/// # Example
///
/// ```ignore
/// #[trust_vc::proof]
/// fn my_lemma(n: u64) {
///     trust_vc::requires!(n > 0);
///     trust_vc::ensures!(n + 1 > n);
/// }
///
/// #[test]
/// fn test_my_lemma() {
///     trust_vc::verify_proof!(my_lemma);
/// }
/// ```
#[doc(hidden)]
pub fn verify_proof_impl(
    func_name: &str,
    module_path: &str,
    file_path: &str,
) -> Result<(), String> {
    try_verify_proof_impl(func_name, module_path, file_path)
        .map_err(|err| legacy_proof_error_message(func_name, module_path, file_path, err))
}

/// Part of #1690: typed inner path returning `TrustVcResult` instead of
/// `Result<(), String>`. Used by crate-internal callers that want structured
/// error context.
pub(crate) fn try_verify_proof_impl(
    func_name: &str,
    module_path: &str,
    file_path: &str,
) -> crate::error::TrustVcResult<()> {
    use crate::VerifyResult;

    match try_verify_function_from_file(file_path, func_name)? {
        VerifyResult::Verified => Ok(()),
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => Err(TrustVcError::Encoding {
            context: "proof verification",
            detail: format!(
                "✗ Verification failed for {}::{}\n  Obligation '{}' failed\n  Counterexample: {}",
                module_path,
                func_name,
                obligation_name,
                model.as_deref().unwrap_or("None")
            ),
        }),
        // A failure, but with no model — so no counterexample is narrated.
        VerifyResult::NotProved { reason, .. } => Err(TrustVcError::Encoding {
            context: "proof verification",
            detail: format!(
                "✗ Verification failed for {}::{}\n  Obligation not proved (no model): {}",
                module_path, func_name, reason
            ),
        }),
        VerifyResult::Unknown { reason, .. } => Err(TrustVcError::Encoding {
            context: "proof verification",
            detail: format!(
                "? Verification unknown for {}::{} ({})",
                module_path, func_name, reason
            ),
        }),
        VerifyResult::Error { message } => Err(TrustVcError::Encoding {
            context: "proof verification",
            detail: format!(
                "Error during verification of {}::{}: {}",
                module_path, func_name, message
            ),
        }),
    }
}

fn legacy_proof_error_message(
    func_name: &str,
    module_path: &str,
    file_path: &str,
    err: TrustVcError,
) -> String {
    match err {
        TrustVcError::Encoding {
            context: "proof verification",
            detail,
        } => detail,
        TrustVcError::Internal {
            context: "proof verification",
            detail,
        } => detail,
        other => format!(
            "Error verifying {}::{}: {}",
            module_path,
            func_name,
            legacy_verify_file_error_message(file_path, other)
        ),
    }
}

fn legacy_verify_file_error_message(file_path: &str, err: TrustVcError) -> String {
    match err {
        TrustVcError::Io { source, .. } => format!("Failed to read file {}: {}", file_path, source),
        TrustVcError::Parse { source, .. } => {
            format!("Failed to parse file {}: {}", file_path, source)
        }
        other => other.into_legacy_string(),
    }
}
