//! Bridge between proc macros and VC extraction pipeline.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Connects proc macro output to the structured verification pipeline.

use crate::context_management::{self, ContextAccessError};
use crate::error::{TrustVcError, TrustVcResult};
#[cfg(feature = "ty")]
use crate::protocol::{ProtocolObligation, TyEncoder};
use crate::vc::{ProofObligation, VerificationContext};
use crate::verification_report::{
    emit_verbose_report_if_enabled, step_from_verify_result, PipelineSummary, VerificationPhase,
    VerificationReport, VerificationReportOptions,
};
use crate::VerifyResult;
use std::cell::RefCell;
use std::time::Instant;

#[path = "verification_bridge_protocol.rs"]
mod protocol_types;

pub(crate) use protocol_types::{
    ProtocolActionDef, ProtocolInvariantDef, ProtocolLivenessDef, ProtocolStateVarDef,
};

#[path = "verification_bridge_parallel.rs"]
mod parallel;

use parallel::finalize_parallel_batch_result;

thread_local! {
    static REGISTERED_PROOFS: RefCell<Vec<ProofRegistration>> = const { RefCell::new(Vec::new()) };
    #[cfg(feature = "ty")]
    static PROTOCOL_OBLIGATIONS: RefCell<Vec<ProtocolObligation>> = const { RefCell::new(Vec::new()) };
    static PROTOCOL_STATE_VARS: RefCell<Vec<ProtocolStateVarDef>> = const { RefCell::new(Vec::new()) };
    static PROTOCOL_ACTIONS: RefCell<Vec<ProtocolActionDef>> = const { RefCell::new(Vec::new()) };
    static PROTOCOL_INVARIANTS: RefCell<Vec<ProtocolInvariantDef>> = const { RefCell::new(Vec::new()) };
    static PROTOCOL_LIVENESS: RefCell<Vec<ProtocolLivenessDef>> = const { RefCell::new(Vec::new()) };
    static COLLECTION_ERROR: RefCell<Option<TrustVcError>> = const { RefCell::new(None) };
}

#[doc(hidden)]
#[derive(Debug, Clone)]
pub(crate) struct ProofRegistration {
    pub(crate) name: String,
    pub(crate) obligations: Vec<ProofObligation>,
}

#[path = "verification_bridge_registry.rs"]
mod registry;

pub(crate) use registry::register_collection_error;
#[cfg(feature = "ty")]
#[doc(hidden)]
pub use registry::register_protocol;
#[doc(hidden)]
pub use registry::{
    clear_registrations, register_proof, register_protocol_action, register_protocol_invariant,
    register_protocol_liveness, register_protocol_state_var,
};

/// Proc-macro verification entry point: collects obligations and dispatches to ay.
#[must_use]
pub struct VerificationPipeline {
    context: VerificationContext,
    collection_error: Option<TrustVcError>,
    registered_proofs: Vec<ProofRegistration>,
    registered_proofs_are_independent: bool,
    #[cfg(feature = "ty")]
    pub protocol_obligations: Vec<ProtocolObligation>,
}

const COLLECTION_ERROR_CONTEXT: &str = "verification bridge collection";

fn collection_error(detail: impl Into<String>) -> TrustVcError {
    TrustVcError::Internal {
        context: COLLECTION_ERROR_CONTEXT,
        detail: detail.into(),
    }
}

fn collection_error_message(err: &TrustVcError) -> String {
    match err {
        TrustVcError::Internal {
            context: COLLECTION_ERROR_CONTEXT,
            detail,
        } => detail.clone(),
        other => other.to_string(),
    }
}

fn context_access_collection_error(err: ContextAccessError) -> TrustVcError {
    collection_error(format!(
        "cannot collect verification state from macros: {}",
        err.message()
    ))
}

fn borrowed_collection_error(state: &'static str) -> TrustVcError {
    collection_error(format!(
        "cannot collect verification state from macros: {state} are already borrowed"
    ))
}

fn take_collection_error() -> TrustVcResult<Option<TrustVcError>> {
    COLLECTION_ERROR.with(|slot| {
        slot.try_borrow_mut()
            .map(|mut slot| slot.take())
            .map_err(|_| borrowed_collection_error("collection errors"))
    })
}

fn extern_spec_bridge_collection_error(err: TrustVcError) -> TrustVcError {
    collection_error(format!("extern_spec bridge import failed: {err}"))
}

fn trait_bridge_collection_error(err: TrustVcError) -> TrustVcError {
    collection_error(format!("trait bridge import failed: {err}"))
}

fn dropped_obligations_unknown(dropped: usize) -> VerifyResult {
    VerifyResult::unknown(
        format!(
            "{} obligation(s) silently dropped due to borrow conflict; verification incomplete (fail-closed guard, #2360)",
            dropped
        ),
        None,
    )
}

fn finalize_verify_result(result: VerifyResult) -> VerifyResult {
    let dropped = crate::obligation_collection::obligations_dropped_count();
    if dropped > 0 {
        crate::obligation_collection::reset_obligations_dropped();
        return dropped_obligations_unknown(dropped);
    }
    result
}

impl Default for VerificationPipeline {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationPipeline {
    /// Create a new empty pipeline.
    pub fn new() -> Self {
        Self {
            context: VerificationContext::new(),
            collection_error: None,
            registered_proofs: Vec::new(),
            registered_proofs_are_independent: false,
            #[cfg(feature = "ty")]
            protocol_obligations: Vec::new(),
        }
    }

    /// Returns a shared reference to the underlying verification context.
    pub fn context(&self) -> &VerificationContext {
        &self.context
    }

    /// Returns a mutable reference to the underlying verification context.
    pub fn context_mut(&mut self) -> &mut VerificationContext {
        &mut self.context
    }

    /// Replaces the verification context and clears registered proof state.
    pub fn replace_context(&mut self, context: VerificationContext) {
        self.context = context;
        self.registered_proofs.clear();
        self.registered_proofs_are_independent = false;
    }

    /// Collect all verification markers from thread-local storage.
    pub fn collect_from_macros() -> Self {
        match Self::collect_from_macros_inner() {
            Ok(pipeline) => pipeline,
            Err(err) => Self {
                context: VerificationContext::new(),
                collection_error: Some(err),
                registered_proofs: Vec::new(),
                registered_proofs_are_independent: false,
                #[cfg(feature = "ty")]
                protocol_obligations: Vec::new(),
            },
        }
    }

    #[cfg(feature = "ty")]
    fn protocol_obligation_count(&self) -> usize {
        self.protocol_obligations.len()
    }

    #[cfg(not(feature = "ty"))]
    fn protocol_obligation_count(&self) -> usize {
        0
    }

    fn collect_from_macros_inner() -> TrustVcResult<Self> {
        let mut pipeline = Self::new();

        // First, get any existing context from verify_macro.
        if let Some(existing_ctx) =
            context_management::try_clone_context().map_err(context_access_collection_error)?
        {
            pipeline.replace_context(existing_ctx);
        }

        if let Some(err) = take_collection_error()? {
            return Err(err);
        }

        // Then add any explicitly registered proofs.
        let registered_proofs = REGISTERED_PROOFS.with(|proofs| {
            proofs
                .try_borrow()
                .map(|proofs| proofs.clone())
                .map_err(|_| borrowed_collection_error("registered proofs"))
        })?;
        pipeline.registered_proofs_are_independent = pipeline.context().obligations().is_empty();
        pipeline.registered_proofs = registered_proofs.clone();
        for registration in &registered_proofs {
            for obligation in &registration.obligations {
                pipeline.context_mut().push_obligation(obligation.clone());
            }
        }
        crate::trait_registry::apply_registered_traits_to_context(pipeline.context_mut())
            .map_err(trait_bridge_collection_error)?;
        crate::extern_spec_verify::apply_extern_specs_to_context(pipeline.context_mut())
            .map_err(extern_spec_bridge_collection_error)?;

        // Collect protocol obligations (ty feature).
        #[cfg(feature = "ty")]
        {
            pipeline.protocol_obligations = PROTOCOL_OBLIGATIONS.with(|proto| {
                proto
                    .try_borrow()
                    .map(|proto| proto.clone())
                    .map_err(|_| borrowed_collection_error("protocol obligations"))
            })?;
        }

        // Assemble protocol components into obligations.
        #[cfg(feature = "ty")]
        protocol_types::assemble_protocol_components(&mut pipeline.protocol_obligations)?;

        // SOUNDNESS-CRITICAL (cardinal false-verify): drop any session-lane
        // `#[broadcast]` lemma axiom whose contract does not establish it.
        // Sibling of the file-path fix in
        // `vc_extraction::suppress_unestablished_broadcast_lemma_axioms`.
        suppress_unestablished_session_broadcast_axioms(&mut pipeline.context);

        Ok(pipeline)
    }

    /// Run the full verification pipeline across ay and ty obligations.
    pub fn verify(&self) -> VerifyResult {
        let options = VerificationReportOptions::from_env();
        if options.verbose() {
            let report = self.verify_with_report(options);
            emit_verbose_report_if_enabled(&report, options);
            return report.result().clone();
        }
        self.verify_internal()
    }

    /// Runs verification and returns a detailed report with per-step diagnostics.
    pub fn verify_with_report(&self, _options: VerificationReportOptions) -> VerificationReport {
        let pipeline = Some(PipelineSummary::from(&self.diagnose()));
        let start = Instant::now();
        if let Some(err) = &self.collection_error {
            return VerificationReport::from_parts(
                VerifyResult::Error {
                    message: collection_error_message(err),
                },
                pipeline,
                Vec::new(),
                start.elapsed(),
            );
        }
        // Empty context is an error - we cannot verify nothing.
        let has_protocol = self.protocol_obligation_count() > 0;

        let smt_report = if let Some(parallel_batch) =
            self.verify_registered_proofs_parallel_batch()
        {
            match parallel_batch {
                Ok(batch_results) => {
                    let smt_result = finalize_parallel_batch_result(&batch_results);
                    let steps = batch_results
                        .into_iter()
                        .map(|(name, result)| {
                            step_from_verify_result(
                                VerificationPhase::ParallelProof,
                                name,
                                None,
                                result.elapsed,
                                &result.result,
                            )
                        })
                        .collect();
                    VerificationReport::from_parts(smt_result, pipeline, steps, start.elapsed())
                }
                Err(result) => {
                    VerificationReport::from_parts(result, pipeline, Vec::new(), start.elapsed())
                }
            }
        } else if self.context().obligations().is_empty() && has_protocol {
            VerificationReport::from_parts(
                VerifyResult::Verified,
                pipeline,
                Vec::new(),
                start.elapsed(),
            )
        } else {
            let report = self
                .context()
                .verify_with_report(VerificationReportOptions::new());
            VerificationReport::from_parts(
                report.result().clone(),
                pipeline,
                report.steps().to_vec(),
                start.elapsed(),
            )
        };

        // Short-circuit: if ay already found a failure, return it
        let smt_result = smt_report.result().clone();
        if !matches!(smt_result, VerifyResult::Verified) {
            return VerificationReport::from_parts(
                finalize_verify_result(smt_result),
                pipeline,
                smt_report.steps().to_vec(),
                start.elapsed(),
            );
        }

        // Protocol path: ty model checker (feature-gated)
        #[cfg(feature = "ty")]
        if self.protocol_obligation_count() > 0 {
            return VerificationReport::from_parts(
                finalize_verify_result(TyEncoder::verify_protocol(&self.protocol_obligations)),
                pipeline,
                smt_report.steps().to_vec(),
                start.elapsed(),
            );
        }

        VerificationReport::from_parts(
            finalize_verify_result(smt_result),
            pipeline,
            smt_report.steps().to_vec(),
            start.elapsed(),
        )
    }

    fn verify_internal(&self) -> VerifyResult {
        if let Some(err) = &self.collection_error {
            return VerifyResult::Error {
                message: collection_error_message(err),
            };
        }
        // Empty context is an error - we cannot verify nothing.
        let has_protocol = self.protocol_obligation_count() > 0;

        let smt_result = if let Some(parallel_result) = self.verify_registered_proofs_parallel() {
            parallel_result
        } else if self.context().obligations().is_empty() && has_protocol {
            VerifyResult::Verified
        } else {
            self.context().verify()
        };

        // Short-circuit: if ay already found a failure, return it
        if !matches!(smt_result, VerifyResult::Verified) {
            return finalize_verify_result(smt_result);
        }

        // Protocol path: ty model checker (feature-gated)
        #[cfg(feature = "ty")]
        if self.protocol_obligation_count() > 0 {
            return finalize_verify_result(TyEncoder::verify_protocol(&self.protocol_obligations));
        }

        finalize_verify_result(smt_result)
    }

    /// Add obligations to the pipeline manually.
    ///
    /// Useful for testing and debugging.
    pub fn add_obligation(&mut self, obligation: ProofObligation) {
        self.context.push_obligation(obligation);
        self.registered_proofs.clear();
        self.registered_proofs_are_independent = false;
    }

    /// Clear all collected obligations.
    pub fn clear(&mut self) {
        self.context = VerificationContext::new();
        self.collection_error = None;
        self.registered_proofs.clear();
        self.registered_proofs_are_independent = false;
        #[cfg(feature = "ty")]
        self.protocol_obligations.clear();
    }

    /// Report queued pipeline state for debugging.
    /// `num_obligations` counts both ay and `ty` work.
    pub fn diagnose(&self) -> PipelineDiagnostic {
        PipelineDiagnostic {
            num_obligations: self.context().obligations().len() + self.protocol_obligation_count(),
            num_variables: self.context().variables().len(),
            has_assertions: self.context().has_assertions(),
            has_assumptions: self.context().has_assumptions(),
        }
    }
}

/// Snapshot of pipeline state used for debugging and reporting.
#[derive(Debug)]
#[must_use = "pipeline diagnostics should be inspected or logged"]
pub struct PipelineDiagnostic {
    num_obligations: usize,
    num_variables: usize,
    has_assertions: bool,
    has_assumptions: bool,
}

impl PipelineDiagnostic {
    /// Returns the total number of proof obligations (ay + ty).
    #[must_use]
    pub const fn num_obligations(&self) -> usize {
        self.num_obligations
    }

    /// Returns the number of declared verification variables.
    #[must_use]
    pub const fn num_variables(&self) -> usize {
        self.num_variables
    }

    /// Returns whether the pipeline contains any assertions.
    #[must_use]
    pub const fn has_assertions(&self) -> bool {
        self.has_assertions
    }

    /// Returns whether the pipeline contains any assumptions.
    #[must_use]
    pub const fn has_assumptions(&self) -> bool {
        self.has_assumptions
    }
}

impl std::fmt::Display for PipelineDiagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Pipeline: {} obligations, {} variables, assertions={}, assumptions={}",
            self.num_obligations(),
            self.num_variables(),
            self.has_assertions(),
            self.has_assumptions()
        )
    }
}

#[cfg(test)]
#[path = "verification_bridge_tests.rs"]
mod tests;

/// Drops every SESSION-lane `#[trust_vc::broadcast]` lemma axiom whose contract
/// does not establish the `ensures` it publishes.
///
/// `broadcast_state.rs` does not build an axiom from parsed source: it EXECUTES
/// the lemma body under `IN_BROADCAST_MODE` and then flips each recorded
/// `ObligationKind::Ensures` in place to `BroadcastAssume`, renaming it
/// `broadcast_*`. An obligation that would have been ASSERTED against the body
/// becomes an ASSUMPTION handed to every caller, and nothing checked it in
/// between — so a lemma whose `ensures` is FALSE of its own body publishes a
/// false axiom, i.e. a contradictory premise that proves anything.
///
/// WHY HERE AND NOT AT THE FLIP. `start_idx` (`BROADCAST_OBLIGATION_START`) is an
/// INDEX into `context.obligations`; verifying mid-harvest, while that index is
/// live, risks invalidating it. Running after collection completes sidesteps that
/// entirely — the same reason the file-path check runs after extraction.
///
/// The check base is the collected context itself, which (unlike the file-path
/// case) ALREADY carries the definitional `__body_axiom_*` obligations; that is
/// what lets an honest lemma over an `#[trust_vc::opaque]` spec fn still verify.
/// `broadcast_lemma_check_child` retains exactly those, REVEALED, and drops every
/// lemma axiom — so no lemma can justify itself or a sibling.
///
/// Vacuity counts as a pass: an unsatisfiable guard makes the published
/// `guard ==> ensures` inert. Every other non-`Verified` verdict drops the axiom.
fn suppress_unestablished_session_broadcast_axioms(ctx: &mut VerificationContext) {
    use crate::vc::{ObligationKind, ProofObligation};

    let candidates: Vec<(String, String, Vec<String>)> = ctx
        .obligations()
        .iter()
        .filter(|o| {
            o.kind() == ObligationKind::BroadcastAssume
                && o.name().starts_with("broadcast_")
                && !o.name().starts_with("__body_axiom_")
        })
        .map(|o| {
            (
                o.name().to_string(),
                o.condition().to_string(),
                o.broadcast_guard
                    .as_ref()
                    .map(|guards| guards.iter().map(|g| g.condition.clone()).collect())
                    .unwrap_or_default(),
            )
        })
        .collect();
    if candidates.is_empty() {
        return;
    }

    let mut unestablished: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for (name, ensures, guards) in candidates {
        let mut child = ctx.broadcast_lemma_check_child();
        for (index, guard) in guards.iter().enumerate() {
            child.push_obligation(ProofObligation::assume(
                format!("__session_lemma_guard_{name}_{index}"),
                guard.clone(),
            ));
        }
        child.push_obligation(ProofObligation::assert(
            format!("__session_lemma_check_{name}"),
            ensures.clone(),
        ));

        let established = match child.verify() {
            VerifyResult::Verified => true,
            VerifyResult::Unknown { category, .. } => {
                matches!(category, crate::encoder::UnknownCategory::VacuousTruth)
            }
            _ => false,
        };
        if !established {
            unestablished.insert(name);
        }
    }

    if !unestablished.is_empty() {
        ctx.retain_obligations(|o| !unestablished.contains(o.name()));
    }
}
