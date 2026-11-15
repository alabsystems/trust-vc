//! Shared confirmation behavior for collection-involving assertions.
//!
//! Provides retry + confirmation wrappers used by both the assertion
//! orchestration path and the inductive-step invariant path.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::panic::AssertUnwindSafe;

use super::assertion::convert_setup_error;
use super::assertion_timeout::{
    forced_timeout_result, verify_assertion_with_timeout_typed,
    verify_assertion_with_timeout_typed_extended,
};
use super::outcome::AssertionOutcome;
use super::panic::{catch_ay_panic_or_resume, catch_encoding_panic_to_unknown};
use super::test_hooks::{force_bv_timeout_enabled, force_extended_retry_success_enabled};
use super::unknown_category::UnknownCategory;
use crate::encoder::AYEncoder;
use crate::error::TrustVcResult;

/// Shared inductive-step assertion attempt with timeout classification and retry.
fn verify_with_confirmation_retry<F>(
    build_encoder: &F,
    assertion: &crate::prepared_context::PreparedObligation,
    rlimit_ms: Option<u64>,
) -> TrustVcResult<AssertionOutcome>
where
    F: Fn() -> TrustVcResult<AYEncoder>,
{
    let initial_outcome = if force_bv_timeout_enabled() {
        forced_timeout_result(&assertion.name)
    } else {
        let encoder = match build_encoder() {
            Ok(enc) => enc,
            Err(err) => return convert_setup_error(err),
        };
        verify_assertion_with_timeout_typed(encoder, assertion, rlimit_ms)?
    };
    match initial_outcome {
        AssertionOutcome::Unknown {
            ref reason,
            category,
            detail,
        } if category.unwrap_or_else(|| UnknownCategory::classify(reason))
            == UnknownCategory::Timeout =>
        {
            let orig = reason.clone();
            let orig_detail = detail;
            let recovered = if force_extended_retry_success_enabled() {
                tracing::info!(assertion = %assertion.name,
                    "Inductive step timeout recovered via extended-timeout retry (forced)");
                Some(AssertionOutcome::Verified)
            } else {
                let recovered = build_encoder()
                    .map_err(|e| {
                        tracing::debug!(assertion = %assertion.name,
                            error = %format!("{e:?}"),
                            "Extended-timeout retry encoder setup failed (inductive step)");
                        e
                    })
                    .ok()
                    .and_then(|encoder| {
                        verify_assertion_with_timeout_typed_extended(encoder, assertion, rlimit_ms)
                            .map_err(|e| {
                                tracing::debug!(assertion = %assertion.name,
                                    error = %format!("{e:?}"),
                                    "Extended-timeout retry failed (inductive step)");
                                e
                            })
                            .ok()
                    })
                    .filter(|o| matches!(o, AssertionOutcome::Verified));
                if recovered.is_some() {
                    tracing::info!(assertion = %assertion.name,
                        "Inductive step timeout recovered via extended-timeout retry");
                }
                recovered
            };
            Ok(recovered.unwrap_or(AssertionOutcome::Unknown {
                reason: orig,
                category: Some(UnknownCategory::Timeout),
                detail: orig_detail,
            }))
        }
        other => Ok(other),
    }
}

/// Protected verification with panic boundary and confirmation check.
///
/// Provides the same reliability guarantees as `verify_single_assertion_typed`
/// but works with a pre-configured encoder (built by `build_encoder` closure).
/// The closure is called once for the main check and once more for
/// confirmation if the context involves collections and the assertion passes.
///
/// Gap closure for #2256, #2354:
/// - Gap 1 (soundness): confirmation check catches ay-dpll non-determinism (#2241)
/// - Gap 2 (robustness): catch_unwind catches ay panics during encoder setup
/// - Gap 3 (scope): context-level collection gate catches mixed contexts (#2354)
pub(in crate::encoder) fn verify_with_confirmation(
    build_encoder: impl Fn() -> TrustVcResult<AYEncoder>,
    assertion: &crate::prepared_context::PreparedObligation,
    context_has_collections: bool,
    rlimit_ms: Option<u64>,
) -> TrustVcResult<AssertionOutcome> {
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        verify_with_confirmation_retry(&build_encoder, assertion, rlimit_ms)
    }));
    match result {
        Ok(inner) => {
            let inner = inner?;
            if matches!(&inner, AssertionOutcome::Verified)
                && (assertion.expr.references_collection() || context_has_collections)
            {
                // Slice 3 of #2706: skip confirmation when a strict proof
                // certificate is available (stronger than a second solver run).
                #[cfg(feature = "proof-certificates")]
                if crate::verification_report::current_proof_is_strict(&assertion.name) {
                    tracing::debug!(
                        assertion = %assertion.name,
                        "skipping inductive-step confirmation — strict proof certificate available"
                    );
                    return Ok(inner);
                }
                #[cfg(test)]
                if super::test_hooks::FORCE_CONFIRMATION_DISAGREE.with(|f| f.get()) {
                    crate::verification_report::record_used_assumptions(&[]);
                    return Ok(AssertionOutcome::Unknown {
                        reason: format!(
                            "Confirmation check disagreed for '{}' (inductive step) \
                             — possible ay-dpll non-determinism (#2241)",
                            assertion.name
                        ),
                        category: Some(UnknownCategory::ConfirmationDisagree),
                        detail: None,
                    });
                }
                let confirm = catch_ay_panic_or_resume(|| {
                    #[cfg(test)]
                    if super::test_hooks::FORCE_CONFIRMATION_PANIC.with(|f| f.get()) {
                        panic!("BUG: mk_eq sort mismatch: expected Bool got BV32");
                    }
                    verify_with_confirmation_retry(&build_encoder, assertion, rlimit_ms)
                });
                match confirm {
                    Ok(Ok(AssertionOutcome::Verified)) => Ok(inner),
                    Ok(Ok(other)) => {
                        crate::verification_report::record_used_assumptions(&[]);
                        Ok(AssertionOutcome::Unknown {
                            reason: format!(
                                "Confirmation check disagreed for '{}' (inductive step): \
                                 the re-solve returned {:?} — fail-closed. That can be a \
                                 genuine solver disagreement (ay #2241), a timeout, or ay \
                                 declining to publish a computed result whose envelope \
                                 expired; read the outcome before attributing it",
                                assertion.name, other
                            ),
                            category: Some(UnknownCategory::ConfirmationDisagree),
                            detail: None,
                        })
                    }
                    Ok(Err(e)) => {
                        crate::verification_report::record_used_assumptions(&[]);
                        Ok(AssertionOutcome::Unknown {
                            reason: format!(
                                "Confirmation check encoder error for '{}' (inductive step): {} \
                                 — re-verification setup failed",
                                assertion.name, e
                            ),
                            category: Some(UnknownCategory::ConfirmationDisagree),
                            detail: None,
                        })
                    }
                    Err(e) => {
                        crate::verification_report::record_used_assumptions(&[]);
                        Ok(AssertionOutcome::Unknown {
                            reason: format!(
                                "Confirmation check ay panic for '{}' (inductive step): {} \
                                 — solver panic during re-verification",
                                assertion.name, e
                            ),
                            category: Some(UnknownCategory::SolverPanic),
                            detail: None,
                        })
                    }
                }
            } else {
                Ok(inner)
            }
        }
        Err(panic_info) => catch_encoding_panic_to_unknown(
            panic_info,
            "ay panic during inductive step encoding for",
            &assertion.name,
        ),
    }
}
