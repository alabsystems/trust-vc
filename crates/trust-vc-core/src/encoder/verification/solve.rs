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
///
/// `solver_panic` is the owning encoder's `VerificationState::solver_panic`:
/// a solve that unwinds poisons the solver, and a poisoned solver is never
/// asked again (see [`poisoned_solver_error`]).
pub(super) fn try_check_sat_with_details(
    solver: &mut Solver,
    solver_panic: &mut Option<String>,
) -> Result<SolveDetails, SolverError> {
    if let Some(first) = solver_panic.as_deref() {
        return Err(poisoned_solver_error(first));
    }
    std::panic::catch_unwind(AssertUnwindSafe(|| {
        #[cfg(test)]
        if super::test_hooks::take_forced_solve_panic() {
            panic!("simulated ay solve panic");
        }
        solver.check_sat_with_details()
    }))
    .map_err(|e| {
        let reason = extract_panic_reason(&*e);
        *solver_panic = Some(reason.clone());
        SolverError::SolverPanic(reason)
    })
}

/// The answer for a solve on a solver whose earlier solve unwound.
///
/// ay does not promise that a `Solver` is usable after a panic inside
/// `check_sat` (its own panic-safe wrappers call it "the poisoned solver"),
/// so the solver is not reused: nothing is solved, and the refusal reads as a
/// solver panic, which no caller turns into a verdict.
pub(super) fn poisoned_solver_error(first_panic: &str) -> SolverError {
    SolverError::SolverPanic(format!(
        "solver not reused: an earlier solve on it panicked ({first_panic})"
    ))
}

/// Record a panic reported by one of ay's own panic-safe `try_check_sat*`
/// wrappers, so the solver it came from is not asked again.
pub(super) fn note_solver_panic<T>(
    result: &Result<T, SolverError>,
    solver_panic: &mut Option<String>,
) {
    if let Err(SolverError::SolverPanic(reason)) = result {
        if solver_panic.is_none() {
            *solver_panic = Some(reason.clone());
        }
    }
}

/// Render an ay `UnknownReason` for a user-facing message.
///
/// THE TWO BUDGET EXHAUSTIONS MUST NOT READ ALIKE. trust-vc bounds every
/// solve twice — a DETERMINISTIC conflict budget (`:rlimit`) and a
/// WALL-CLOCK liveness backstop (`set_timeout`) — and a user debugging a
/// failure needs to know which one fired, because the remedies are opposite:
/// "raise `#[verifier::rlimit]`, this proof genuinely needs more work" versus
/// "your machine was too slow / something is hanging, and the verdict you got
/// is not a property of your program". ay's own Display already separates
/// them (`resourceout` vs `timeout`); this expands `resourceout` so the
/// distinction survives into the message a user actually reads.
pub(super) fn format_unknown_reason(reason: Option<UnknownReason>) -> String {
    match reason {
        Some(UnknownReason::ResourceLimit) => {
            "resourceout — deterministic conflict budget exhausted (#[verifier::rlimit])"
                .to_string()
        }
        Some(reason) => reason.to_string(),
        None => "unspecified".to_string(),
    }
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

/// ay's own attribution, on the solve envelope, for "the independent
/// model-check gate refuted the model I had just produced".
///
/// `unknown.phase` is the broad attribution set by
/// `Executor::downgrade_sat_after_gate`; `model_check_gate.result` is the
/// narrow verdict set by `apply_independent_model_gate` /
/// `apply_strict_model_gate` immediately before it. Either alone is sufficient
/// evidence, and the pair is what ay sets together on the `ModelViolates`
/// path. (`SolveDetails::unknown_diagnostic.phase` is the same
/// `unknown.phase` string, typed — `ay-dpll/src/api/solving/controls.rs`
/// `build_unknown_diagnostic` reads it from exactly this statistic — so it is
/// consulted first and the raw statistic is the fallback.)
///
/// `confirmed-sat` and `cannot-confirm` are deliberately NOT matched: the first
/// is a model the gate ACCEPTED, the second a coverage gap where the gate could
/// not decide. Only `model-violates` means the gate ground-falsified an
/// assertion under ay's own published model.
pub(super) const AY_MODEL_GATE_PHASE: &str = "independent-model-check-gate";
pub(super) const AY_MODEL_GATE_VIOLATES: &str = "model-violates";

/// Evidence that ay caught its own invalid model on this solve.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ModelGateRejection {
    /// The assertion ay's gate ground-falsified under ay's own model, when ay
    /// named it (`model_check_gate.violated_assertion`).
    pub(super) violated_assertion: Option<String>,
}

/// Read ay's gate attribution off a solve envelope.
///
/// MEASURED CAVEAT, 2026-09-17 (`docs/ay-defect-2026-09-17-quantified-axiom-family.md`
/// section 12): for the *quantified definitional axiom* trigger these keys do
/// NOT survive to `check_sat_with_details` at the measured ay revision — the
/// gate fires on an ay-INTERNAL sub-solve whose statistics are restored away
/// before the outer envelope is built. `model_check_gate.result` reaches
/// trust-vc there only with the value `confirmed-sat`. This reader is
/// nevertheless the correct consumer half, is exercised directly by
/// `unknown_category_tests`, and becomes live the moment ay preserves the
/// attribution. It is deliberately NOT a heuristic on the banner text: the
/// banner goes to ay's stderr and is not part of any API.
pub(super) fn model_gate_rejection(details: &SolveDetails) -> Option<ModelGateRejection> {
    model_gate_rejection_from_stats(
        &details.statistics,
        details
            .unknown_diagnostic
            .as_ref()
            .and_then(|d| d.phase.as_deref()),
    )
}

/// The decision itself, split out from [`SolveDetails`] because that type is
/// `#[non_exhaustive]` in ay and therefore cannot be constructed in a trust-vc
/// test. `Statistics` can (it is `Default` with a public `set_string`), so this
/// seam is pinned against a REAL `Statistics` carrying ay's real key names —
/// not against a hand-rolled parts tuple that could drift from them.
pub(super) fn model_gate_rejection_from_stats(
    statistics: &ay_dpll::Statistics,
    typed_phase: Option<&str>,
) -> Option<ModelGateRejection> {
    let by_phase =
        typed_phase.or_else(|| statistics.get_string("unknown.phase")) == Some(AY_MODEL_GATE_PHASE);
    let by_gate = statistics.get_string("model_check_gate.result") == Some(AY_MODEL_GATE_VIOLATES);
    if !(by_phase || by_gate) {
        return None;
    }
    Some(ModelGateRejection {
        violated_assertion: statistics
            .get_string("model_check_gate.violated_assertion")
            .map(ToOwned::to_owned),
    })
}

/// Relabel an already-classified unknown as [`UnknownCategory::ModelGateRejected`]
/// when — and ONLY when — that relabel cannot move a verdict.
///
/// # Why this is a guard and not an unconditional override
///
/// ay sets `last_unknown_reason = UnknownReason::Incomplete` on the gate
/// downgrade, which the reason-code mapping calls `Incompleteness` — "the
/// decision procedure cannot decide this", which is not what happened. The gate
/// attribution is the more specific fact and should win.
///
/// But ay's gate keys and a RESOURCE reason can in principle arrive on the same
/// envelope (a gate rejection followed by a timeout on the same solve). An
/// UNCONDITIONAL override would then turn a resource `Unknown` — a non-failure,
/// because a timeout does not mean the fact is false — into a `NotProved`
/// FAILURE. That is precisely the soundness boundary of
/// `design-unknown-as-failure.md`, crossed in the wrong direction, by a change
/// that was supposed to move no verdicts at all.
///
/// So the relabel is confined to the incompleteness class. Both the input and
/// the output category are then `is_incompleteness()`, `VerifyResult::unknown`
/// routes on exactly that predicate, and the verdict is therefore identical by
/// construction — not by inspection. A resource unknown keeps its own category
/// and stays a soft `Unknown` even when the gate fired.
pub(super) fn gate_relabelled_category(
    base: UnknownCategory,
    gate_rejected: bool,
) -> UnknownCategory {
    if gate_rejected && base.is_incompleteness() {
        UnknownCategory::ModelGateRejected
    } else {
        base
    }
}

/// The user-facing explanation appended when ay caught its own invalid model.
///
/// It must NOT read as "your proof is wrong". The obligation is undecided, and
/// the thing that was shown false is ay's own candidate witness.
pub(super) fn render_model_gate_rejection(rejection: &ModelGateRejection) -> String {
    let mut out = String::from(
        " — NOT a refutation: ay's independent model-check gate refuted the model ay \
         itself produced and fail-closed Sat -> Unknown (ay behaving correctly; an \
         ay-side defect, not a defect in this proof)",
    );
    if let Some(term) = &rejection.violated_assertion {
        let term: String = term.chars().take(300).collect();
        out.push_str(&format!(
            ". Assertion falsified under ay's own model: {term}"
        ));
    }
    out
}

pub(super) fn solver_unknown_outcome(
    assertion_name: &str,
    location: Option<&str>,
    reason: Option<UnknownReason>,
    gate: Option<&ModelGateRejection>,
) -> AssertionOutcome {
    let loc_suffix = location.map(|loc| format!(" at {loc}")).unwrap_or_default();
    let reason_str = format_unknown_reason(reason);
    let gate_suffix = gate.map(render_model_gate_rejection).unwrap_or_default();
    let rendered_reason = format!(
        "Solver returned unknown ({reason_str}) for '{assertion_name}'{loc_suffix}{gate_suffix}"
    );
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
    let category = gate_relabelled_category(
        classify_unknown_reason(reason, &rendered_reason),
        gate.is_some(),
    );
    AssertionOutcome::unknown_with_detail(rendered_reason.clone(), Some(category), detail)
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
        // The constant evaluator reads declared types as the encoder does: a
        // goal the one typing validator refuses is not evaluated (§5b rule
        // 13) but left to the encoding, which refuses it: unvalidated, `Cast {
        // 3132225413u32, from_ty: char, to_ty: u64 } != -12` was decided
        // `Verified` here.
        let const_eval = if self.validate_ir_typing(&assertion.expr, None).is_ok() {
            Self::try_const_eval_typed(&assertion.expr, ctx_width)
        } else {
            None
        };
        match const_eval {
            Some(true) => return Ok(AssertionOutcome::Verified),
            Some(false)
                if self.state.assumption_count == 0
                    && self.state.unpruned_proof_fact_count == 0 =>
            {
                return Ok(AssertionOutcome::Counterexample {
                    obligation_name: assertion.display_name().to_string(),
                    location: assertion.location.clone(),
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
                    // The predicates assumed below, for the certificate: terms
                    // trust-vc posed, proved by the separate check, which records
                    // no certificate of its own.
                    #[cfg(feature = "proof-certificates")]
                    let mut assumed_lemmas: Vec<ay_core::TermId> = Vec::new();

                    // Assert+Assume pattern (Verus OverflowBehavior): overflow predicates
                    // were already verified in a separate encoder. Re-encode here to get
                    // the predicates in this solver's term universe and assume them so
                    // downstream reasoning can rely on the absence of overflow. Part of #2516.
                    //
                    // ASSUME ONLY WHAT WAS CHECKED. The overflow CHECK that
                    // justifies this block is gated per OBLIGATION, and this
                    // block reads the same gate:
                    //
                    // * a `by(nonlinear_arith)` goal skips the check outright
                    //   (`verify_single_assertion_typed_inner`), and the shared
                    //   BV lane refuses it, so NOTHING is assumed for it — not
                    //   even the `Div`/`Rem` or collection predicates the Int
                    //   lane still emits;
                    // * for every other goal the check runs with
                    //   `exec_arith_overflow_in_scope` as its arithmetic flag,
                    //   and the re-encode below passes the same flag, so the
                    //   assumed predicate set is the checked one. A
                    //   `by(bit_vector)` goal or a spec-arithmetic obligation
                    //   (`ensures`, `requires`, a calc step, a call-site
                    //   precondition) therefore assumes its collection
                    //   preconditions, which were checked, and no arithmetic
                    //   no-overflow predicate, which was not.
                    //
                    // Assuming an unchecked predicate makes a goal pinned where
                    // the arithmetic really overflows vacuous:
                    // `requires x == 3, y == 86; ensures x - y == 0` (u8, exec)
                    // came back `Verified` (tests/operand_signedness_proptest.rs).
                    //
                    // Nothing is assumed in a demand-inline retry
                    // (`demand_inlined_bodies`): the separate pass checked the
                    // assertion without those bodies expanded.
                    if self.state.overflow_behavior.should_check()
                        && !super::assertion::is_nonlinear_arith_mode(assertion.solver_mode)
                        && !self.state.demand_inlined_bodies
                    {
                        let saved_lengths = self.collection_lengths.clone();
                        let overflow_result = self.resolve_condition_with_overflow_typed(
                            &assertion.expr,
                            super::assertion::exec_arith_overflow_in_scope(true, assertion),
                        );
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
                            #[cfg(feature = "proof-certificates")]
                            assumed_lemmas.push(pred.id());
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

                    let mut details = match try_check_sat_with_details(
                        &mut self.solver,
                        &mut self.state.solver_panic,
                    ) {
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
                        let fallback = self.solver.try_check_sat_assuming_with_details(&[negated]);
                        note_solver_panic(&fallback, &mut self.state.solver_panic);
                        if let Ok(fb) = fallback {
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
                            // #2654: bind the refutation to the obligation whose
                            // negation was asserted into THIS scope. `assertion`
                            // is that obligation — it is the same value whose
                            // `negated` goal was pushed above — so the identity is
                            // read off the query, never inferred from which report
                            // step happens to be open. Sub-queries (conjunct
                            // splits) carry their own derived names and are
                            // therefore refused attachment to the parent step.
                            //
                            // The certificate's premises are bound to the query
                            // trust-vc posed, whose negated goal is `negated`,
                            // and the kernel runs on it; only then may it claim
                            // to be checked evidence for `assertion`. Premises
                            // among the assumed predicates are counted.
                            let solver = &self.solver;
                            let assumed_lemmas = &assumed_lemmas;
                            verification_report::record_proof_artifact(
                                &artifact,
                                || {
                                    verification_report::kernel_bridge::certify_last_refutation(
                                        solver,
                                        negated,
                                        assumed_lemmas,
                                    )
                                },
                                &assertion.name,
                            );
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
                        // Capture the SAME published model before any disposable
                        // broadcast replay changes the solver's current query.
                        // Function bodies are display DATA, never evidence for
                        // changing the verdict or relaxing the witness guards.
                        let published_model = self.solver.try_get_model_str();
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

                            let mut model_str = model.as_ref().map(|m| {
                                super::model_render::format_counterexample_model(
                                    m,
                                    &self.var_types,
                                    &self.counterexample_var_meta,
                                )
                            });
                            let mut bindings = model
                                .as_ref()
                                .map(|m| {
                                    super::model_render::collect_counterexample_bindings(
                                        m,
                                        &self.var_types,
                                        &self.counterexample_var_meta,
                                    )
                                })
                                .unwrap_or_default();
                            let functions = match published_model {
                                Ok(document) => super::model_render::published_function_bindings(
                                    &document,
                                    &self.counterexample_var_meta,
                                )
                                .map_err(str::to_string),
                                Err(error) => Err(error.to_string()),
                            };
                            match functions {
                                Ok(functions) if !functions.is_empty() => {
                                    let rendered = functions
                                        .iter()
                                        .map(|binding| {
                                            format!("{} = {}", binding.display_name, binding.value)
                                        })
                                        .collect::<Vec<_>>()
                                        .join("\n");
                                    model_str = Some(
                                        if model.as_ref().is_some_and(|m| m.model().is_empty()) {
                                            rendered
                                        } else {
                                            format!("{}\n{rendered}", model_str.unwrap_or_default())
                                        },
                                    );
                                    bindings.extend(functions);
                                }
                                Err(reason) => {
                                    model_str = Some(format!(
                                        "{}\nFunction interpretations unavailable: {reason}",
                                        model_str.unwrap_or_default()
                                    ));
                                }
                                _ => {}
                            }
                            Ok(AssertionOutcome::Counterexample {
                                obligation_name: assertion.display_name().to_string(),
                                location: assertion.location.clone(),
                                model: model_str,
                                bindings,
                            })
                        }
                    } else {
                        let gate = model_gate_rejection(&details);
                        Ok(solver_unknown_outcome(
                            &assertion.name,
                            assertion.location.as_deref(),
                            details.unknown_reason,
                            gate.as_ref(),
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
