//! Parallel verification for independent proof registrations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::encoder::AYEncoder;
use crate::prepared_context::prepare_context;
use crate::BatchVerifyResult;
use crate::VerifyResult;

use super::VerificationPipeline;

#[cfg(test)]
use std::cell::Cell;

#[cfg(test)]
thread_local! {
    static PARALLEL_VERIFY_OVERRIDE: Cell<Option<bool>> = const { Cell::new(None) };
}

pub(super) fn parallel_verify_enabled() -> bool {
    #[cfg(test)]
    if let Some(enabled) = PARALLEL_VERIFY_OVERRIDE.with(|override_flag| override_flag.get()) {
        return enabled;
    }

    std::env::var_os("TRUST_VC_PARALLEL_VERIFY").is_some()
}

#[cfg(test)]
pub(super) fn with_parallel_verify_override<T>(enabled: bool, f: impl FnOnce() -> T) -> T {
    PARALLEL_VERIFY_OVERRIDE.with(|override_flag| {
        let prior = override_flag.replace(Some(enabled));
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        override_flag.set(prior);
        match result {
            Ok(result) => result,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    })
}

impl VerificationPipeline {
    pub(super) fn verify_registered_proofs_parallel(&self) -> Option<VerifyResult> {
        match self.verify_registered_proofs_parallel_batch()? {
            Ok(batch_results) => Some(finalize_parallel_batch_result(&batch_results)),
            Err(result) => Some(result),
        }
    }

    pub(super) fn verify_registered_proofs_parallel_batch(
        &self,
    ) -> Option<Result<Vec<(String, BatchVerifyResult)>, VerifyResult>> {
        if !parallel_verify_enabled()
            || !self.registered_proofs_are_independent
            || self.registered_proofs.len() <= 1
            || self.context().obligations().len() != self.registered_proof_obligation_count()
        {
            return None;
        }

        let mut prepared_contexts = Vec::with_capacity(self.registered_proofs.len());
        for registration in &self.registered_proofs {
            let mut proof_context = self.context.clone();
            proof_context.obligations = registration.obligations.clone();
            match prepare_context(&proof_context) {
                Ok(prepared) => prepared_contexts.push(prepared),
                Err(err) => {
                    return Some(Err(VerifyResult::Error {
                        message: format!(
                            "parallel proof preparation failed for `{}`: {}",
                            registration.name, err
                        ),
                    }));
                }
            }
        }

        let mut batch_results = AYEncoder::verify_batch_parallel(prepared_contexts);
        batch_results.sort_by_key(|result| result.index());
        let named_results = self
            .registered_proofs
            .iter()
            .map(|registration| registration.name.clone())
            .zip(batch_results)
            .collect();
        Some(Ok(named_results))
    }

    fn registered_proof_obligation_count(&self) -> usize {
        self.registered_proofs
            .iter()
            .map(|registration| registration.obligations.len())
            .sum()
    }
}

pub(super) fn finalize_parallel_batch_result(
    batch_results: &[(String, BatchVerifyResult)],
) -> VerifyResult {
    batch_results
        .iter()
        .map(|(_, result)| result.result().clone())
        .find(|result| !matches!(result, VerifyResult::Verified))
        .unwrap_or(VerifyResult::Verified)
}
