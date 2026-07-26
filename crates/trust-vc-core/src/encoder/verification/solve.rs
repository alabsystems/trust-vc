//! Panic-safe solve envelope and assertion-result decoding for ay solver calls.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::panic::AssertUnwindSafe;

use ay_dpll::api::{SolveDetails, Solver, SolverError};
use ay_dpll::UnknownReason;

use super::outcome::{AdaptiveQuantifierRetryClass, AssertionOutcome, SolverUnknownDetail};
use super::panic::{extract_panic_reason, is_ay_panic, is_sort_mismatch_error};
use super::test_hooks::{force_empty_model_enabled, take_forced_scope_pop_failure};
use super::unknown_category::UnknownCategory;
use crate::encoder::diagnostics::{EncodingApproximation, EncodingDiagnostics};
use crate::encoder::AYEncoder;
#[cfg(feature = "named-assertions")]
use crate::encoder::VerificationState;
use crate::error::{TrustVcError, TrustVcResult};
use crate::verification_report;

/// Run `check_sat_with_details()` with panic safety, returning the atomic
/// solve envelope that bundles result + statistics + unknown reason +
/// verification summary in a single call.
///
/// Replaces the previous `try_observe_check_sat()` which called
/// `try_check_sat()` then separately pulled statistics and unknown reason.
/// The atomic API ensures all metadata is captured from the same solve call.
/// Part of #2242.
pub(super) fn try_check_sat_with_details(solver: &mut Solver) -> Result<SolveDetails, SolverError> {
    std::panic::catch_unwind(AssertUnwindSafe(|| solver.check_sat_with_details()))
        .map_err(|e| SolverError::SolverPanic(extract_panic_reason(&*e)))
}

pub(super) fn format_unknown_reason(reason: Option<UnknownReason>) -> String {
    reason
        .map(|reason| reason.to_string())
        .unwrap_or_else(|| "unspecified".to_string())
}

/// True iff a candidate SAT model pins NO concrete-sorted value — every
/// concrete value map (int/real/bool/bitvector/string/floating-point/seq/array/
/// datatype) is empty. It may still carry uninterpreted-sort (`Poly`)
/// placeholders, or be entirely empty.
///
/// A genuine refutation assigns concrete values to every concrete-sorted free
/// variable of the negated goal, so the absence of any concrete witness marks a
/// model that carries no falsifying concrete evidence — the under-constrained
/// shape produced by the generic spec-fn-return type-erasure incompleteness.
/// See the guard in [`AYEncoder::verify_assertion_typed`]. Part of #2778.
fn model_has_no_concrete_witness(model: &ay_dpll::api::Model) -> bool {
    model.iter_ints().next().is_none()
        && model.iter_reals().next().is_none()
        && model.iter_bools().next().is_none()
        && model.iter_bvs().next().is_none()
        && model.iter_strings().next().is_none()
        && model.iter_fps().next().is_none()
        && model.iter_seqs().next().is_none()
        && model.iter_arrays().next().is_none()
        && model.iter_datatypes().next().is_none()
}

pub(super) fn classify_unknown_reason(
    reason: Option<UnknownReason>,
    fallback_reason: &str,
) -> UnknownCategory {
    UnknownCategory::from_unknown_reason(reason)
        .unwrap_or_else(|| UnknownCategory::classify(fallback_reason))
}

pub(super) fn solver_unknown_outcome(
    assertion_name: &str,
    location: Option<&str>,
    reason: Option<UnknownReason>,
) -> AssertionOutcome {
    let loc_suffix = location.map(|loc| format!(" at {loc}")).unwrap_or_default();
    let reason_str = format_unknown_reason(reason);
    let rendered_reason =
        format!("Solver returned unknown ({reason_str}) for '{assertion_name}'{loc_suffix}");
    let detail = SolverUnknownDetail::from_unknown_reason(reason);
    if let Some(detail) = detail {
        let retry_class = detail.adaptive_quantifier_retry_class();
        match retry_class {
            AdaptiveQuantifierRetryClass::BudgetPressureRetriable => tracing::debug!(
                assertion = assertion_name,
                unknown_detail = ?detail,
                budget_retriable = detail.is_budget_retriable(),
                "adaptive retry groundwork observed budget-retriable quantifier unknown"
            ),
            AdaptiveQuantifierRetryClass::PermanentlyNonRetriable => tracing::debug!(
                assertion = assertion_name,
                unknown_detail = ?detail,
                budget_retriable = detail.is_budget_retriable(),
                "adaptive retry groundwork observed permanently non-retriable quantifier unknown"
            ),
            AdaptiveQuantifierRetryClass::Other => {}
        }
    }
    AssertionOutcome::unknown_with_detail(
        rendered_reason.clone(),
        Some(classify_unknown_reason(reason, &rendered_reason)),
        detail,
    )
}

pub(super) fn format_solver_observation_error(
    context: impl Into<String>,
    error: SolverError,
) -> String {
    let context = context.into();
    match error {
        SolverError::SolverPanic(reason) => {
            format!("{context}: ay solver panic: {reason}")
        }
        other => format!("{context}: {other}"),
    }
}

pub(super) fn format_solver_scope_pop_warning(assertion_name: &str, error: &SolverError) -> String {
    format!(
        "failed to pop solver scope after '{}': {}",
        assertion_name, error
    )
}

#[cfg(feature = "named-assertions")]
pub(super) fn record_used_assumptions_from_unsat_core(
    solver: &Solver,
    state: &VerificationState,
    query: &str,
) {
    match solver.try_get_unsat_core() {
        Ok(core) => {
            let used = state.used_assumptions_from_core(&core);
            verification_report::record_used_assumptions(&used);
        }
        Err(error) => tracing::debug!(
            query,
            error = ?error,
            "failed to extract UNSAT core for named assertion diagnostics"
        ),
    }
}

/// Classify a failure while installing overflow assumptions in the scoped
/// solver frame (ROOT B of the 2026-07-18 corpus-red triage).
///
/// Encode/assert-stage failures here are DETERMINISTIC: the obligation's
/// expression could not be turned into a well-formed solver term (undefined
/// function/sort, unsupported cast/construct, malformed term). No amount of
/// solver fuel, retry budget, or quantifier escalation can ever make such an
/// obligation solvable, so the stable fail-closed verdict is `Error` with the
/// original diagnostic preserved. `Unknown` is reserved for genuine solver
/// INCOMPLETENESS (timeout / incomplete quantifier / resource-out — see
/// docs/design-unknown-as-failure.md), which can only arise from a
/// `check_sat`, never from encoding; plus the ay backend panic classes (sort
/// mismatch / BUG-marker panics) that the engine deliberately swallows as
/// `Unknown(SolverPanic)`. This mirrors the refutation-encode discipline in
/// `verify_assertion_typed` directly below, which already fails closed (via
/// `TrustVcError::Encoding`) for exactly this class of failure — only this
/// overflow-assumption path used to demote it to `Unknown(Other)`.
fn overflow_scope_failure(
    assertion_name: &str,
    stage: &str,
    detail: impl Into<String>,
) -> AssertionOutcome {
    let detail = detail.into();
    tracing::warn!(
        assertion = %assertion_name,
        stage,
        error = %detail,
        "failed to install overflow assumptions in scoped solver frame"
    );
    let message = format!(
        "Failed to {stage} overflow assumptions for '{}': {}",
        assertion_name, detail
    );
    if is_sort_mismatch_error(&detail) || is_ay_panic(&detail) {
        AssertionOutcome::unknown(message, Some(UnknownCategory::SolverPanic))
    } else {
        AssertionOutcome::Error { message }
    }
}

fn try_pop_solver_scope(solver: &mut Solver) -> Result<(), SolverError> {
    if take_forced_scope_pop_failure() {
        return Err(SolverError::SolverPanic(
            "forced scope pop failure for test coverage".to_string(),
        ));
    }
    solver.try_pop()
}

pub(super) fn demote_verified_outcome(
    outcome: AssertionOutcome,
    target: &str,
    diagnostics: &EncodingDiagnostics,
) -> AssertionOutcome {
    if matches!(outcome, AssertionOutcome::Verified) && diagnostics.has_demoting() {
        AssertionOutcome::unknown(
            diagnostics.demotion_reason(target),
            Some(UnknownCategory::EncodingDemotion),
        )
    } else {
        outcome
    }
}

impl AYEncoder {
    /// Core single-assertion verification on a configured encoder.
    ///
    /// Renamed from `verify_assertion_typed_classified` — the category is now
    /// embedded in `AssertionOutcome::Unknown` instead of being a separate
    /// tuple element. Part of #1690.
    pub(super) fn verify_assertion_typed(
        &mut self,
        assertion: &crate::prepared_context::PreparedObligation,
    ) -> TrustVcResult<AssertionOutcome> {
        #[cfg(debug_assertions)]
        super::timeout::IN_TIMEOUT_CONTEXT.with(|flag| {
            debug_assert!(
                flag.get(),
                "verify_assertion_typed() called outside timeout context — \
                 use verify_assertion_with_timeout_typed() instead (#1705)"
            );
        });

        let ctx_width = self.infer_int_width();
        match Self::try_const_eval_typed(&assertion.expr, ctx_width) {
            Some(true) => return Ok(AssertionOutcome::Verified),
            Some(false)
                if self.state.assumption_count == 0
                    && self.state.unpruned_proof_fact_count == 0 =>
            {
                let display = assertion.display_name();
                let obligation_name = match &assertion.location {
                    Some(loc) => format!("{} (at {})", display, loc),
                    None => display.to_string(),
                };
                return Ok(AssertionOutcome::Counterexample {
                    obligation_name,
                    model: None,
                    bindings: Vec::new(),
                });
            }
            Some(false) => {}
            None => {}
        }

        if let Err(e) = self.solver.try_push() {
            self.state.reusable_after_scope = false;
            return Ok(AssertionOutcome::unknown(
                format!(
                    "ay error creating solver scope for '{}': {}",
                    assertion.name, e
                ),
                Some(UnknownCategory::SolverPanic),
            ));
        }

        let scoped_result: TrustVcResult<AssertionOutcome> = crate::encoder::with_flag_unwind_safe!(
            self.state.active_solver_mode,
            assertion.solver_mode,
            {
                (|| {
                    // Assert+Assume pattern (Verus OverflowBehavior): overflow predicates
                    // were already verified in a separate encoder. Re-encode here to get
                    // the predicates in this solver's term universe and assume them so
                    // downstream reasoning can rely on the absence of overflow. Part of #2516.
                    if self.state.overflow_behavior.should_check() {
                        let saved_lengths = self.collection_lengths.clone();
                        let overflow_result =
                            self.resolve_condition_with_overflow_typed(&assertion.expr, true);
                        self.collection_lengths = saved_lengths;
                        let (_, overflow_preds) = match overflow_result {
                            Ok(result) => result,
                            Err(error) => {
                                return Ok(overflow_scope_failure(
                                    &assertion.name,
                                    "encode",
                                    error.to_string(),
                                ));
                            }
                        };

                        for (_, pred) in &overflow_preds {
                            if let Err(error) = self.solver.try_assert_term(*pred) {
                                return Ok(overflow_scope_failure(
                                    &assertion.name,
                                    "assert",
                                    error.to_string(),
                                ));
                            }
                        }
                    }

                    let nested_alternation_before = self
                        .state
                        .diagnostics
                        .count(EncodingApproximation::NestedExistentialAlternation);
                    let negated = match self.resolve_refutation_condition_typed(&assertion.expr) {
                        Ok(n) => n,
                        Err(e) => {
                            let msg = format!(
                                "Failed to encode refutation for '{}': {}",
                                assertion.name, e
                            );
                            if is_sort_mismatch_error(&e) {
                                return Ok(AssertionOutcome::unknown(msg, None));
                            }
                            if is_ay_panic(&e.to_string()) {
                                return Ok(AssertionOutcome::unknown(msg, None));
                            }
                            return Err(TrustVcError::Encoding {
                                context: "encode assertion refutation",
                                detail: msg,
                            });
                        }
                    };
                    // A witness-dependent `exists v. (... forall ...)` refutes to
                    // an exact alternating `forall-exists` query. AY can decide
                    // that shape unreliably and, on the known native
                    // quantifier-expansion path, may not honor its deadline at
                    // all. The encoder records a demoting approximation while
                    // constructing the exact refutation above. If this assertion
                    // introduced one, return the only sound supported verdict
                    // before asserting or solving the query: deterministic
                    // `Unknown(EncodingDemotion)`.
                    //
                    // Compare counts rather than testing the cumulative
                    // diagnostics set so an earlier obligation cannot suppress
                    // an unrelated later solve.
                    if self
                        .state
                        .diagnostics
                        .count(EncodingApproximation::NestedExistentialAlternation)
                        > nested_alternation_before
                    {
                        return Ok(AssertionOutcome::unknown(
                            self.state.diagnostics.demotion_reason(&assertion.name),
                            Some(UnknownCategory::EncodingDemotion),
                        ));
                    }
                    #[cfg(feature = "named-assertions")]
                    let assert_negated_result = {
                        let solver_name = self
                            .state
                            .register_negated_target_core_name(assertion.display_name());
                        self.solver.try_assert_named(negated, &solver_name)
                    };
                    #[cfg(not(feature = "named-assertions"))]
                    let assert_negated_result = self.solver.try_assert_term(negated);
                    if let Err(e) = assert_negated_result {
                        let msg = format!(
                            "Failed to assert negated condition for '{}': {}",
                            assertion.name, e
                        );
                        if is_ay_panic(&e.to_string()) {
                            return Ok(AssertionOutcome::unknown(msg, None));
                        }
                        return Err(TrustVcError::Encoding {
                            context: "assert negated condition",
                            detail: msg,
                        });
                    }

                    match self.flush_ground_axioms_to_fixpoint() {
                        Ok(total_instantiations) => {
                            if self.state.ground_pool.needs_flush() {
                                self.state.diagnostics.record(
                            crate::encoder::diagnostics::EncodingApproximation::GroundFixpointNonConvergence,
                        );
                                tracing::warn!(
                                    assertion = %assertion.name,
                                    instantiations = total_instantiations,
                                    "Ground pool fixpoint did not converge within round limit",
                                );
                            }
                        }
                        Err(e) => {
                            let msg = format!(
                                "Failed to flush ground axioms for '{}': {}",
                                assertion.name, e
                            );
                            if is_sort_mismatch_error(&e) {
                                return Ok(AssertionOutcome::unknown(msg, None));
                            }
                            return Err(TrustVcError::Encoding {
                                context: "flush ground axioms",
                                detail: msg,
                            });
                        }
                    }

                    let mut details = match try_check_sat_with_details(&mut self.solver) {
                        Ok(details) => details,
                        Err(error) => {
                            return Ok(AssertionOutcome::unknown(
                                format_solver_observation_error(
                                    format!("ay error checking '{}'", assertion.name),
                                    error,
                                ),
                                Some(UnknownCategory::SolverPanic),
                            ));
                        }
                    };
                    tracing::debug!(
                        assertion = %assertion.name,
                        result = ?details.result.result(),
                        verification_level = %details.verification_level,
                        unknown_reason = ?details.unknown_reason,
                        model_validated = details.verification.sat_model_validated,
                        conflicts = details.statistics.conflicts,
                        decisions = details.statistics.decisions,
                        propagations = details.statistics.propagations,
                        restarts = details.statistics.restarts,
                        learned_clauses = details.statistics.learned_clauses,
                        deleted_clauses = details.statistics.deleted_clauses,
                        theory_conflicts = details.statistics.theory_conflicts,
                        theory_propagations = details.statistics.theory_propagations,
                        num_vars = details.statistics.num_vars,
                        num_clauses = details.statistics.num_clauses,
                        num_assertions = details.statistics.num_assertions,
                        term_bytes = self.solver.instance_term_bytes(),
                        "solver stats"
                    );
                    verification_report::record_solve_details(
                        &details,
                        Some(self.solver.instance_term_bytes()),
                    );

                    // Incremental push-scope completeness fallback (#enum-incremental).
                    //
                    // ay's incremental solve is incomplete for some datatype/BV
                    // obligations when the negated goal is asserted inside a
                    // `(push)` scope: the SAME formula (cs0 ∧ ¬goal) decided at base
                    // scope, or via the assumption mechanism, is UNSAT, yet the
                    // pushed-scope `check_sat` returns Unknown (fail-closed, never a
                    // false Verified). This bites the composite-return ENUM accept
                    // obligation (`Verdict { Reject, Accept(i128) }`), whose lowering
                    // is a native datatype sort carrying a nested-`Ite` BitVec128
                    // payload. The low-level base/push/assuming regression and
                    // genuine-SAT control live with the source fix in AY's
                    // `ay-dpll/tests/pushscope_repro.rs`; Trust-VC pins the live
                    // end-to-end path in
                    // `tests/ay_incumbent_accept_composite_enum.rs`.
                    //
                    // Recover by re-solving the IDENTICAL query through
                    // `check_sat_assuming([negated])`, which uses the assumption
                    // mechanism instead of a fresh push frame and decides it.
                    //
                    // SOUNDNESS: `check_sat_assuming(A)` returns UNSAT iff the
                    // currently-asserted set together with `A` is unsatisfiable. The
                    // assumption `negated` is the exact refutation condition already
                    // asserted in this scope, so the query is bit-for-bit
                    // (cs0 ∧ ¬goal) under the SAME long-lived solver and its FULL
                    // native datatype/BV theory — no weakening, no fresh encoding.
                    // It can therefore only turn a fail-closed Unknown into the
                    // genuine verdict; it can never fabricate a false UNSAT (false
                    // Verified) nor suppress a real counterexample. We adopt the
                    // fallback result only when it is definitive (UNSAT, or a
                    // model-validated SAT); a still-Unknown / unvalidated-SAT
                    // fallback leaves the original fail-closed Unknown in place.
                    if details.result.result().is_unknown() {
                        if let Ok(fb) = self.solver.try_check_sat_assuming_with_details(&[negated])
                        {
                            let fb_result = fb.solve.result.result();
                            if fb_result.is_unsat()
                                || (fb_result.is_sat() && fb.solve.verification.sat_model_validated)
                            {
                                tracing::debug!(
                                    assertion = %assertion.name,
                                    fallback_result = ?fb_result,
                                    "enum-incremental: pushed-scope Unknown re-solved \
                                     definitively via check_sat_assuming",
                                );
                                details = fb.solve;
                            }
                        }
                    }

                    let solve_result = details.result.result();
                    if solve_result.is_unsat() {
                        #[cfg(feature = "named-assertions")]
                        record_used_assumptions_from_unsat_core(
                            &self.solver,
                            &self.state,
                            &assertion.name,
                        );
                        #[cfg(feature = "proof-certificates")]
                        if let Some(artifact) = self.solver.export_last_unsat_artifact() {
                            let ay_proof = self.solver.last_proof();
                            verification_report::record_proof_artifact(&artifact, ay_proof);
                        }
                        Ok(AssertionOutcome::Verified)
                    } else if solve_result.is_sat() {
                        // Demote unvalidated Sat to Unknown — ay may produce
                        // spurious counterexamples when model validation fails.
                        // Structural defense against #2241. Phase 2 of #2242.
                        if !details.verification.sat_model_validated {
                            let loc_suffix = assertion
                                .location
                                .as_deref()
                                .map(|l| format!(" at {}", l))
                                .unwrap_or_default();
                            return Ok(AssertionOutcome::unknown(
                                format!(
                                    "sat model not validated by ay for '{}'{}",
                                    assertion.name, loc_suffix
                                ),
                                Some(UnknownCategory::ModelNotValidated),
                            ));
                        }
                        let condition_has_quantifier =
                            assertion.expr.has_non_skolemized_quantifier();
                        let statically_refuted_exists =
                            super::super::ir_encoder::refutation::statically_refutes_finite_exists(
                                &assertion.expr,
                            );
                        let loc_suffix = assertion
                            .location
                            .as_deref()
                            .map(|l| format!(" at {}", l))
                            .unwrap_or_default();
                        let model = match self.solver.try_get_model() {
                            Ok(model) => Some(model),
                            Err(e) => {
                                return Ok(AssertionOutcome::unknown(
                                    format!(
                                        "ay error getting model for '{}'{}: {}",
                                        assertion.name, loc_suffix, e
                                    ),
                                    None,
                                ));
                            }
                        };
                        if condition_has_quantifier
                            && !statically_refuted_exists
                            && (force_empty_model_enabled()
                                || model.as_ref().is_none_or(|m| m.model().is_empty()))
                        {
                            Ok(AssertionOutcome::unknown(
                                format!(
                                    "Solver returned SAT with empty model for '{}'{} \
                                 — treating as unknown (ay-dpll CEGQI limitation)",
                                    assertion.name, loc_suffix
                                ),
                                Some(UnknownCategory::EmptyModel),
                            ))
                        } else {
                            // Soundness #1: ay's model validation SKIPS quantified
                            // assertions, so a SAT model marked `sat_model_validated`
                            // can still violate an un-instantiated broadcast `forall`
                            // premise. Re-validate the candidate model against those
                            // premises before promoting it to a definitive
                            // counterexample. Instantiating a premise at the model's
                            // witnesses adds only logical *consequences* of the
                            // already-asserted forall, so an UNSAT re-check is a sound
                            // Verified (the original SAT model was spurious). Any other
                            // re-check result keeps the original counterexample — this
                            // can neither suppress a genuine refutation nor fabricate a
                            // false Verified (see broadcast_model_revalidation docs).
                            use super::broadcast_model_revalidation::BroadcastModelRevalidation;
                            if !self.state.broadcast_premises.is_empty() {
                                if let Some(witness) = model.as_ref().map(|m| m.model().clone()) {
                                    if let BroadcastModelRevalidation::Refuted =
                                        self.revalidate_broadcast_premises_against_model(&witness)
                                    {
                                        return Ok(AssertionOutcome::Verified);
                                    }
                                }
                            }

                            // Generic spec-fn-return incompleteness guard (#2778).
                            //
                            // A transparent `#[spec]` fn with a `TypeParam` return is
                            // encoded over the type-erased `Poly` sort with Box/Unbox;
                            // its definitional body axiom (`f(x) == x`) is a `forall`
                            // whose bound variable is Poly-sorted. ay's ground
                            // instantiation can fail to fire that axiom at the Poly
                            // witness a counterexample assigns, leaving the
                            // monomorphized return projection (`projected.a`)
                            // under-constrained. The returned SAT model then pins NO
                            // concrete witness (only an uninterpreted Poly placeholder,
                            // or is empty) yet "refutes" a goal whose truth hinges on
                            // the un-fired axiom — a false refutation.
                            //
                            // Degrade such a body-axiom-unvalidated model to an
                            // Unknown — the SAME graceful-degradation policy and the
                            // SAME `EmptyModel` category as the empty-model CEGQI guard
                            // directly above (this model is empty of *concrete*
                            // witnesses) — when BOTH:
                            //   (1) this query erased a struct/enum value through a
                            //       Box/Unbox DATATYPE bridge (`has_datatype_bridge`),
                            //       AND
                            //   (2) the candidate model pins no concrete value (only
                            //       uninterpreted Poly placeholders, or is empty).
                            //
                            // `EmptyModel` (not `Incompleteness`) is deliberate: it is
                            // the established empty-model degradation class, and it is
                            // NOT `is_incompleteness()`, so the concrete-compute
                            // recovery in `finish_regular_assertion_step` does not fire
                            // on it. The SMT path genuinely cannot decide this
                            // (type-erasure CEGQI gap), so the honest result is Unknown
                            // — never an SMT Counterexample, and never upgraded to a
                            // Verified off a fully-ground concrete-compute fallback.
                            //
                            // SOUNDNESS: a genuine refutation assigns concrete values
                            // to every concrete-sorted free variable of the negated
                            // goal, so a model with no concrete witness carries no
                            // falsifying concrete evidence; downgrading it can never
                            // manufacture a Verified and is strictly fail-closed. It
                            // never masks the cases that MUST refute: a real datatype
                            // refutation pins a concrete `datatype_values` witness, so
                            // (2) is false and the counterexample stands; and SCALAR
                            // generic returns (e.g. `identity::<u64>(5) == 6`, the
                            // opaque-tagged `hidden::<bool>(t, 4) == 5`) decide through
                            // a real theory and are excluded by the datatype-bridge
                            // conjunct (1). The guard is thus confined to the
                            // generic-datatype field-projection shape this work
                            // unblocks.
                            if self.registries.poly_context.has_datatype_bridge() {
                                if let Some(m) = model.as_ref() {
                                    if model_has_no_concrete_witness(m.model()) {
                                        return Ok(AssertionOutcome::unknown(
                                            format!(
                                                "Solver returned an under-constrained (no concrete \
                                                 witness) empty model for '{}'{} — a generic \
                                                 spec-fn return whose definitional body axiom was \
                                                 not instantiated over the type-erased Poly sort \
                                                 (treating as unknown)",
                                                assertion.name, loc_suffix
                                            ),
                                            Some(UnknownCategory::EmptyModel),
                                        ));
                                    }
                                }
                            }

                            let model_str = model.as_ref().map(|m| {
                                super::model_render::format_counterexample_model(
                                    m,
                                    &self.var_types,
                                    &self.counterexample_var_meta,
                                )
                            });
                            let bindings = model
                                .as_ref()
                                .map(|m| {
                                    super::model_render::collect_counterexample_bindings(
                                        m,
                                        &self.var_types,
                                        &self.counterexample_var_meta,
                                    )
                                })
                                .unwrap_or_default();
                            let display = assertion.display_name();
                            let obligation_name = match &assertion.location {
                                Some(loc) => format!("{} (at {})", display, loc),
                                None => display.to_string(),
                            };
                            Ok(AssertionOutcome::Counterexample {
                                obligation_name,
                                model: model_str,
                                bindings,
                            })
                        }
                    } else {
                        Ok(solver_unknown_outcome(
                            &assertion.name,
                            assertion.location.as_deref(),
                            details.unknown_reason,
                        ))
                    }
                })()
            }
        );

        if let Err(error) = try_pop_solver_scope(&mut self.solver) {
            self.state.reusable_after_scope = false;
            tracing::warn!(
                assertion = %assertion.name,
                error = %error,
                "{}",
                format_solver_scope_pop_warning(&assertion.name, &error),
            );
        }
        let result = scoped_result?;

        Ok(demote_verified_outcome(
            result,
            &assertion.name,
            &self.state.diagnostics,
        ))
    }
}

#[cfg(test)]
#[path = "solve_tests.rs"]
mod tests;
