//! Panic classification and panic boundary handling for ay solver panics.
//!
//! This module is the trust_vc adapter surface for the canonical ay_core panic
//! helpers. Classification logic lives upstream in ay_core::panic_utils;
//! this module delegates to those helpers and provides trust-vc-specific
//! error mapping (TrustVcError::Encoding, AssertionOutcome::Unknown).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::panic::AssertUnwindSafe;

use super::outcome::AssertionOutcome;
use super::unknown_category::UnknownCategory;
use crate::error::{TrustVcError, TrustVcResult};

/// Extract a human-readable reason string from a panic payload.
///
/// Delegates to [`ay_core::panic_payload_to_string`].
pub(in crate::encoder) fn extract_panic_reason(payload: &(dyn std::any::Any + Send)) -> String {
    ay_core::panic_payload_to_string(payload)
}

/// Check whether a panic reason matches known ay internal panic patterns.
///
/// Delegates to [`ay_core::is_ay_panic_reason`].
pub(in crate::encoder) fn is_ay_panic(reason: &str) -> bool {
    ay_core::is_ay_panic_reason(reason)
}

/// Check whether a reason string indicates a sort mismatch error.
///
/// This is a trust-vc-local helper that classifies both panic payloads and
/// formatted diagnostic strings. Kept local because it operates on
/// solver error Display output, not just raw panic payloads.
pub(in crate::encoder) fn is_sort_mismatch_error(reason: impl std::fmt::Display) -> bool {
    let reason_lower = reason.to_string().to_lowercase();
    let reason_compact: String = reason_lower
        .chars()
        .filter(|c| !c.is_ascii_whitespace())
        .collect();
    reason_lower.contains("sort mismatch")
        || reason_compact.contains("sortmismatch")
        || reason_lower.contains("expects bool, got")
}

/// Catch panics from `f`, but only swallow ay-classified panics as
/// `Err(TrustVcError::Encoding)`. Non-ay panics (programmer errors) are
/// resumed immediately so they propagate to the test harness or crash the
/// process as intended.
///
/// Delegates to [`ay_core::catch_ay_panics`] for the unwind boundary and
/// panic classification, then maps ay panic reasons into the trust_vc error
/// type.
///
/// Part of #2330, #1690, #1731.
pub(in crate::encoder) fn catch_ay_panic_or_resume<T, F>(f: F) -> TrustVcResult<T>
where
    F: FnOnce() -> T,
{
    ay_core::catch_ay_panics(AssertUnwindSafe(|| Ok(f())), |reason| {
        Err(TrustVcError::Encoding {
            context: "ay solver panic",
            detail: reason,
        })
    })
}

/// Catch panics from `f` and convert ay-classified panics into
/// `AssertionOutcome::Unknown`. Non-ay panics propagate via `resume_unwind`.
///
/// This is used by the thread-body verification paths that need to return
/// `TrustVcResult<AssertionOutcome>` directly rather than `TrustVcResult<T>`.
#[cfg(test)]
pub(in crate::encoder) fn catch_ay_sort_panics<F>(f: F) -> TrustVcResult<AssertionOutcome>
where
    F: FnOnce() -> TrustVcResult<AssertionOutcome> + std::panic::UnwindSafe,
{
    ay_core::catch_ay_panics(f, |reason| {
        Ok(AssertionOutcome::Unknown {
            reason: format!("ay solver panic: {reason}"),
            category: Some(UnknownCategory::SolverPanic),
            detail: None,
        })
    })
}

/// Catch panics and convert ay-classified panics into
/// `TrustVcResult<AssertionOutcome>` with a contextual assertion name.
///
/// Used by the inline thread bodies in the timeout verification paths.
pub(in crate::encoder) fn catch_ay_panic_to_unknown(
    panic_payload: Box<dyn std::any::Any + Send>,
    assertion_name: &str,
) -> TrustVcResult<AssertionOutcome> {
    let reason = extract_panic_reason(&*panic_payload);
    if !is_ay_panic(&reason) {
        std::panic::resume_unwind(panic_payload);
    }
    Ok(AssertionOutcome::Unknown {
        reason: format!("ay solver panic for '{}': {}", assertion_name, reason),
        category: Some(UnknownCategory::SolverPanic),
        detail: None,
    })
}

/// Catch panics from the encoding phase and convert ay-classified panics
/// into `AssertionOutcome::Unknown` with an assertion-specific message.
///
/// Used by `verify_single_assertion_typed` and `verify_with_confirmation`.
pub(in crate::encoder) fn catch_encoding_panic_to_unknown(
    panic_payload: Box<dyn std::any::Any + Send>,
    prefix: &str,
    assertion_name: &str,
) -> TrustVcResult<AssertionOutcome> {
    let reason = extract_panic_reason(&*panic_payload);
    if !is_ay_panic(&reason) {
        std::panic::resume_unwind(panic_payload);
    }
    Ok(AssertionOutcome::Unknown {
        reason: format!("{prefix} '{}': {}", assertion_name, reason),
        category: Some(UnknownCategory::SolverPanic),
        detail: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::TrustVcError;

    // ========================================================================
    // TrustVc-specific delegation behavior tests
    // ========================================================================

    #[test]
    fn test_extract_panic_reason_str() {
        let payload: Box<dyn std::any::Any + Send> = Box::new("sort mismatch");
        assert_eq!(extract_panic_reason(&*payload), "sort mismatch");
    }

    #[test]
    fn test_extract_panic_reason_string() {
        let payload: Box<dyn std::any::Any + Send> = Box::new(String::from("BUG: mk_eq failed"));
        assert_eq!(extract_panic_reason(&*payload), "BUG: mk_eq failed");
    }

    #[test]
    fn test_extract_panic_reason_non_string() {
        let payload: Box<dyn std::any::Any + Send> = Box::new(42i32);
        // ay_core returns "unknown panic" for non-string payloads
        assert_eq!(extract_panic_reason(&*payload), "unknown panic");
    }

    #[test]
    fn test_is_ay_panic_sort_mismatch() {
        assert!(is_ay_panic("sort mismatch: expected Bool, got BV(8)"));
        assert!(is_ay_panic("Sort Mismatch in term construction"));
        assert!(is_ay_panic("SORT MISMATCH"));
    }

    #[test]
    fn test_is_ay_panic_non_ay_panics() {
        assert!(!is_ay_panic("index out of bounds"));
        assert!(!is_ay_panic("assertion failed"));
        assert!(!is_ay_panic("debug: some info"));
    }

    #[test]
    fn test_is_sort_mismatch_error_variants() {
        assert!(is_sort_mismatch_error(
            "sort mismatch: expected Bool, got BV(8)"
        ));
        assert!(is_sort_mismatch_error(
            "SortMismatch { operation: \"try_eq\", expected: \"Bool\", got: [Int, Bool] }"
        ));
        assert!(is_sort_mismatch_error("Term expects Bool, got Int"));
        assert!(!is_sort_mismatch_error("division by zero"));
    }

    #[test]
    fn test_is_sort_mismatch_error_accepts_display_types() {
        let err = TrustVcError::Encoding {
            context: "encode trigger",
            detail: "SortMismatch { operation: \"try_eq\", expected: \"Bool\", got: [Int, Bool] }"
                .to_string(),
        };
        assert!(is_sort_mismatch_error(&err));
    }

    // ========================================================================
    // catch_ay_sort_panics — trust-vc-specific boundary behavior
    // ========================================================================

    #[test]
    fn test_catch_ay_sort_panics_ok_result() {
        let result = catch_ay_sort_panics(|| Ok(AssertionOutcome::Verified));
        assert!(matches!(result, Ok(AssertionOutcome::Verified)));
    }

    #[test]
    fn test_catch_ay_sort_panics_err_result() {
        let result = catch_ay_sort_panics(|| {
            Err(TrustVcError::Encoding {
                context: "test panic boundary",
                detail: "solver timeout".to_string(),
            })
        });
        assert!(matches!(result, Err(TrustVcError::Encoding { .. })));
    }

    #[test]
    fn test_catch_ay_sort_panics_catches_ay_panic() {
        let result = catch_ay_sort_panics(std::panic::AssertUnwindSafe(|| {
            panic!("sort mismatch: expected Bool, got BV(8)");
        }));
        match result {
            Ok(AssertionOutcome::Unknown {
                reason, category, ..
            }) => {
                assert!(
                    reason.contains("ay solver panic"),
                    "Expected ay panic message, got: {reason}"
                );
                assert!(
                    reason.contains("sort mismatch"),
                    "Expected sort mismatch in reason, got: {reason}"
                );
                assert_eq!(category, Some(UnknownCategory::SolverPanic));
            }
            other => panic!("Expected Unknown error, got: {other:?}"),
        }
    }

    #[test]
    fn test_catch_ay_sort_panics_reraises_non_ay_panic() {
        let result = std::panic::catch_unwind(|| {
            catch_ay_sort_panics(std::panic::AssertUnwindSafe(|| {
                panic!("index out of bounds: the len is 3 but the index is 5");
            }))
        });
        assert!(
            result.is_err(),
            "Non-ay panics must propagate through catch_ay_sort_panics"
        );
    }

    // ========================================================================
    // catch_ay_panic_or_resume — trust_vc TrustVcError mapping
    // ========================================================================

    #[test]
    fn test_catch_ay_panic_or_resume_swallows_ay_panic() {
        let result = catch_ay_panic_or_resume(|| {
            panic!("Sort mismatch: expected Bool, got BV(8)");
        });
        match result {
            Err(err) => {
                let msg = err.to_string();
                assert!(
                    msg.contains("Sort mismatch"),
                    "ay-classified panic should be captured as Err: {}",
                    msg
                );
            }
            Ok(_) => panic!("should not return Ok for a panicking closure"),
        }
    }

    #[test]
    #[should_panic(expected = "programmer error: index out of bounds")]
    fn test_catch_ay_panic_or_resume_resumes_non_ay_string_panic() {
        let _: TrustVcResult<()> = catch_ay_panic_or_resume(|| {
            panic!("programmer error: index out of bounds");
        });
    }

    #[test]
    #[should_panic]
    fn test_catch_ay_panic_or_resume_resumes_non_string_payload() {
        let _: TrustVcResult<()> = catch_ay_panic_or_resume(|| {
            std::panic::panic_any(42_i32);
        });
    }
}
