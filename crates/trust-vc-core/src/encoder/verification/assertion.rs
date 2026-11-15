//! Single-assertion verification orchestration and retry cascade.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;
use std::panic::AssertUnwindSafe;

use super::assertion_timeout::{
    forced_timeout_result, verify_assertion_with_timeout_reuse,
    verify_assertion_with_timeout_typed, verify_assertion_with_timeout_typed_extended,
    ReuseAttempt,
};
use super::outcome::AssertionOutcome;
use super::overflow::check_overflow_predicates;
use super::panic::{catch_encoding_panic_to_unknown, is_ay_panic};
use super::solve::demote_verified_outcome;
use super::test_hooks::{force_bv_timeout_enabled, force_extended_retry_success_enabled};
use super::unknown_category::UnknownCategory;
use super::VerificationSlices;
use crate::encoder::diagnostics::EncodingDiagnostics;
use crate::encoder::AYEncoder;
use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::TrustVcExpr;
use crate::prepared_context::PreparedObligation;
use crate::vc::{ObligationKind, VariableDecl};

/// Convert typed setup/build errors into internal verification outcomes when
/// they represent ay limitations rather than hard infrastructure failures.
pub(super) fn convert_setup_error(err: TrustVcError) -> TrustVcResult<AssertionOutcome> {
    match err {
        TrustVcError::Encoding {
            context: "ay solver panic",
            detail,
        } if is_ay_panic(&detail) => Ok(AssertionOutcome::unknown(
            format!("ay solver panic: {detail}"),
            Some(UnknownCategory::SolverPanic),
        )),
        other => Err(other),
    }
}

/// Name prefix for the synthetic obligation minted by the broadcast-vacuity
/// probe. The probe re-verifies the *negation* of a just-verified goal in the
/// same context; this prefix both documents the synthetic origin and guards
/// against the probe ever recursing into itself (see
/// `vacuity_probe_result`).
pub(super) const VACUITY_PROBE_PREFIX: &str = "__vacuity_probe_";

/// True iff a *genuine* `#[broadcast]` lemma assumption (not a definitional
/// spec-function body axiom) is active in this context.
///
/// `broadcast_assumptions` holds every `BroadcastAssume` obligation. Spec
/// functions emit a definitional `__body_axiom_<fn>` (`f(x) == body`) which is
/// consistent by construction and therefore can never make a goal vacuously
/// true. Restricting the (relatively expensive) vacuity probe to contexts that
/// carry a real broadcast lemma keeps it from perturbing the thousands of
/// ordinary spec-function obligations while still covering exactly the class of
/// assumption that can publish a contradictory premise — a `#[broadcast]` proof
/// fn whose `ensures!` is republished as a global axiom WITHOUT verifying the
/// body establishes it.
pub(super) fn context_has_broadcast_lemma(slices: &VerificationSlices<'_>) -> bool {
    slices
        .broadcast_assumptions
        .iter()
        .any(|obligation| !obligation.name.contains("__body_axiom_"))
}

/// True iff this context publishes a TRAIT-METHOD postcondition as a global
/// universal axiom (SOUNDNESS-CRITICAL gate — see [`vacuity_probe_result`]).
///
/// `register_trait` emits every trait method `ensures` as an unconditional
/// `∀ self, args. requires ⟹ ensures[result := Trait__m(self, args)]`
/// (`assert_trait_postconditions`), and `register_trait_impl` does the same for
/// an impl's own `ensures` (`assert_impl_postcondition_axioms`,
/// `assert_impl_trait_ensures_concrete_axioms`). Those axioms land in the SAME
/// solver context that discharges an ordinary caller's obligations
/// (`setup::…`), and — exactly like a `#[broadcast]` lemma — nothing in the
/// caller's own query establishes them.
///
/// The premise this class can inject is not merely unproven, it can be
/// UNREALIZABLE. `ensures(result > x)` over `u32` has NO total interpretation
/// (nothing is `bvult`-above `u32::MAX`), so the axiom is UNSAT standing alone;
/// under it, `t.p(u32::MAX) == 5` and `t.p(u32::MAX) != 5` were BOTH reported
/// `Verified`. The conformance obligation does not backstop this: with no impl
/// in the file there is no conformance obligation at all, and with an impl the
/// caller's own verdict is still the one reported.
///
/// Why this predicate and not "any universal axiom": a DEFINITIONAL axiom
/// (`f(args) == body`, and the seq/set/map/array structural axioms) is
/// consistent by construction — it defines a function, so a model always
/// exists. A POSTCONDITION axiom constrains a UF by an arbitrary user
/// predicate and may pin it to a value that does not exist. Free functions emit
/// no postcondition axiom at all (`register_function_context` publishes only
/// signature metadata), so this class is exactly the trait surface.
pub(super) fn context_publishes_trait_postcondition_axiom(slices: &VerificationSlices<'_>) -> bool {
    let ctx = slices.ctx;
    ctx.trait_decls
        .iter()
        .any(|decl| decl.methods.iter().any(|m| !m.ensures.is_empty()))
        || ctx
            .trait_impl_method_ensures
            .values()
            .any(|ensures| !ensures.is_empty())
}

/// True iff the context carries at least one premise that was published as a
/// global axiom WITHOUT this query verifying it — the only premise classes that
/// can be contradictory, and therefore the exact gate for the vacuity probe.
///
/// Two members, both confirmed to have produced a false `Verified`:
/// a `#[broadcast]` lemma ([`context_has_broadcast_lemma`]) and a trait-method
/// postcondition ([`context_publishes_trait_postcondition_axiom`]).
pub(super) fn context_publishes_unverified_axiom(slices: &VerificationSlices<'_>) -> bool {
    context_has_broadcast_lemma(slices) || context_publishes_trait_postcondition_axiom(slices)
}

/// True iff the goal expression contains any quantifier (`forall`/`exists`),
/// at the top level or nested.
///
/// For such a goal the broadcast-vacuity probe re-verifies the *negation* `¬G`,
/// which re-encodes `G` positively as a real solver quantifier. ay's CEGQI/MBQI
/// then frequently returns `Unknown` instead of a definitive UNSAT (vacuous) or
/// SAT-model (consistent) — the asymmetry that let a contradictory `#[broadcast]`
/// lemma prove a universally-quantified FALSE goal while the probe punted to
/// `Unknown`. Ground goals do not have this asymmetry, so they keep the precise
/// `Verified`-only downgrade (no over-rejection). Part of the P2 vacuity fix.
fn goal_contains_quantifier(expr: &TrustVcExpr) -> bool {
    use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};

    struct QuantifierFinder {
        found: bool,
    }
    impl TrustVcExprVisitor for QuantifierFinder {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            if self.found {
                return;
            }
            if matches!(expr, TrustVcExpr::Quantifier { .. }) {
                self.found = true;
                return;
            }
            walk_expr(self, expr);
        }
    }

    let mut finder = QuantifierFinder { found: false };
    finder.visit_expr(expr);
    finder.found
}

/// Builds the synthetic negated-goal obligation for the vacuity probe.
///
/// Keeps every field of the original goal (kind, bound vars, triggers, solver
/// mode, …) so the negation is encoded in the *same* arithmetic/quantifier mode
/// as the goal it shadows; only the name, condition string, and expression are
/// changed (the expression is wrapped in a logical `Not`). `step_meta` is
/// cleared so the synthetic probe never participates in calc-step accounting.
fn negated_probe_obligation(assertion: &PreparedObligation) -> PreparedObligation {
    let mut probe = assertion.clone();
    probe.name = format!("{VACUITY_PROBE_PREFIX}{}", assertion.name);
    probe.condition = format!("!({})", assertion.condition);
    probe.expr = TrustVcExpr::Not(Box::new(assertion.expr.clone()));
    probe.step_meta = None;
    probe
}

/// Vacuity probe (SOUNDNESS-CRITICAL).
///
/// trust-vc proves a goal `G` when `assumptions ∧ ¬G` is UNSAT (i.e.
/// `assumptions ⊨ G`). Two premise classes reach that query as global axioms
/// that the query itself never establishes, and either can be CONTRADICTORY —
/// under which BOTH `G` and `¬G` are provable and `G` verifies vacuously, a
/// CATASTROPHIC false `Verified` that proves false:
///
///  1. a `#[broadcast]` lemma, which publishes its `ensures!` as a global
///     `forall` axiom without verifying the body establishes it (a bogus
///     `ensures!(x * x < 0)` is contradictory outright); and
///  2. a TRAIT-METHOD postcondition, which `register_trait` publishes as
///     `∀ self, args. ensures[result := Trait__m(self, args)]`. This one is
///     worse than merely unproven — it can be UNREALIZABLE, i.e. UNSAT with no
///     impl anywhere able to satisfy it. `ensures(result > x)` over `u32` is
///     such a contract, and it made `t.p(u32::MAX) == 5` AND
///     `t.p(u32::MAX) != 5` both report `Verified`. See
///     [`context_publishes_trait_postcondition_axiom`].
///
/// Class 2 has no other backstop. `check_vacuous_truth` screens only
/// ASSUMPTION-level premises (`VerificationSlices::new(ctx, assumptions,
/// broadcast, &[], &[], &[])` — empty goal slices) and additionally returns
/// early when the assumption set is empty, so a setup-level axiom is never
/// screened; and E-matching only instantiates the axiom once a ground
/// `Trait__m(..)` term appears, which in this class comes from the GOAL. That
/// is precisely why the check must run here, against the goal, rather than in
/// the precheck. Nor does the conformance obligation cover it: with no impl in
/// the file `list_trait_conformance_obligations` is EMPTY, and with an impl the
/// caller's own verdict is still what is reported.
///
/// This probe is consulted whenever a goal transitions to `Verified` AND such a
/// premise is in scope. It re-verifies the *negated* goal `¬G` in the
/// identical context. If `¬G` ALSO verifies, then `assumptions ⊨ G` and
/// `assumptions ⊨ ¬G` simultaneously, which is possible only if the assumptions
/// are contradictory — so the original `G` was vacuously true. We then downgrade
/// to `Unknown(VacuousTruth)` (fail-closed).
///
/// Soundness / no over-rejection: when the assumptions are CONSISTENT, at most
/// one of `G` / `¬G` can be valid, so the probe's negated check fails (returns a
/// counterexample/Unknown) and the genuine `Verified` is preserved. The probe
/// can therefore only ever fire on a genuinely contradictory assumption set; it
/// never turns a soundly-proven goal into a failure. Recursion is impossible:
/// the synthetic obligation is named with `VACUITY_PROBE_PREFIX` and the probe
/// returns early for any such obligation, and the probe re-enters only
/// `verify_single_assertion_typed_with_extra_variables` (never a goal-finishing
/// path that would re-invoke the probe).
///
/// Returns `Some(Unknown(VacuousTruth))` when the goal is vacuous, `None`
/// otherwise (the caller keeps the original `Verified`).
pub(in crate::encoder) fn vacuity_probe_result(
    slices: &VerificationSlices<'_>,
    assertion: &PreparedObligation,
    extra_variables: &[VariableDecl],
    post_loop_modified_vars: Option<&HashSet<String>>,
) -> Option<AssertionOutcome> {
    // Recursion guard: never probe the probe's own synthetic obligation.
    if assertion.name.starts_with(VACUITY_PROBE_PREFIX) {
        return None;
    }
    // Only run when the context publishes a premise it did not verify — a
    // genuine broadcast lemma (not a definitional body axiom) or a trait-method
    // postcondition axiom. Those are the only premise classes that can be
    // contradictory; definitional axioms are consistent by construction.
    if !context_publishes_unverified_axiom(slices) {
        return None;
    }

    let probe = negated_probe_obligation(assertion);
    // Capture-suppressed so the probe's internal verification adds no obligation
    // steps / fingerprints to the report (keeps obligation accounting unchanged).
    let probe_outcome = crate::verification_report::with_capture_suppressed(|| {
        verify_single_assertion_typed_with_extra_variables(
            slices,
            &probe,
            post_loop_modified_vars,
            extra_variables,
        )
    });

    // A definitive refutation of ¬G (a genuine Counterexample, i.e. a concrete
    // model of `assumptions ∧ G`) is a positive consistency witness: the
    // assumptions admit a model in which G holds, so the original `Verified` is
    // sound and must be preserved (no over-rejection).
    if matches!(probe_outcome, Ok(AssertionOutcome::Counterexample { .. })) {
        return None;
    }

    // `¬G` ALSO verifies ⇒ `assumptions ⊨ G` and `assumptions ⊨ ¬G` ⇒ the
    // assumptions are contradictory ⇒ the original `Verified` was vacuous.
    let negation_also_verified = matches!(probe_outcome, Ok(AssertionOutcome::Verified));

    // For a QUANTIFIED goal the probe re-encodes `G` positively as a real solver
    // quantifier and ay's CEGQI/MBQI frequently returns `Unknown` instead of a
    // definitive verdict — so a contradictory broadcast lemma proved the FALSE
    // universal goal `G` while `¬G` punted to `Unknown`, leaving the vacuous
    // `Verified` in place. Treat any NON-REFUTED probe outcome (`Unknown`/`Error`
    // / encode error included) conservatively for such goals: there is no
    // consistency witness, so fail closed rather than trust the unprovable
    // negation. Ground goals keep the precise `Verified`-only rule (the probe is
    // decidable there, so a non-refutation cannot be a false negative).
    let quantified_goal_not_refuted =
        goal_contains_quantifier(&assertion.expr) && !negation_also_verified;

    if negation_also_verified || quantified_goal_not_refuted {
        // Name the class that is actually in scope so the diagnostic points at
        // the premise the user must fix. Both may be present; report both.
        let mut culprits: Vec<&str> = Vec::new();
        if context_has_broadcast_lemma(slices) {
            culprits.push(
                "a #[broadcast] lemma whose `ensures!` is republished as a global axiom \
                 without its body being verified to establish it",
            );
        }
        if context_publishes_trait_postcondition_axiom(slices) {
            culprits.push(
                "a trait-method `ensures` published as a global axiom \
                 `forall self, args. ensures[result := Trait__m(self, args)]` — check that \
                 the contract is SATISFIABLE at all (e.g. `ensures(result > x)` over `u32` \
                 has no solution at `x == u32::MAX`, so NO impl can ever satisfy it)",
            );
        }
        let culprit_text = culprits.join("; and ");
        tracing::warn!(
            assertion = %assertion.name,
            negation_also_verified,
            "vacuity probe: the negated goal was not refuted under the published \
             axioms; downgrading the (potentially vacuous) Verified"
        );
        return Some(AssertionOutcome::unknown(
            format!(
                "Goal '{}' may be vacuously true: the negated goal could not be refuted, \
                 so there is no consistency witness for this context's premises. In scope: \
                 {culprit_text}. A contradictory premise makes every goal trivially \
                 provable, so the proof is rejected rather than trusted.",
                assertion.name
            ),
            Some(UnknownCategory::VacuousTruth),
        ));
    }

    None
}

/// Applies the vacuity probe to a verification `result`, downgrading a vacuous
/// `Verified` to `Unknown(VacuousTruth)`. A no-op for any non-`Verified`
/// outcome or `Err`. Wired into every goal->Verified chokepoint
/// (`finish_regular_assertion_step` and `verify_typed_step`). Part of the
/// unverified-axiom soundness gate.
pub(in crate::encoder) fn apply_vacuity_probe_to_result(
    result: TrustVcResult<AssertionOutcome>,
    slices: &VerificationSlices<'_>,
    assertion: &PreparedObligation,
    extra_variables: &[VariableDecl],
    post_loop_modified_vars: Option<&HashSet<String>>,
) -> TrustVcResult<AssertionOutcome> {
    match result {
        Ok(AssertionOutcome::Verified) => {
            Ok(
                vacuity_probe_result(slices, assertion, extra_variables, post_loop_modified_vars)
                    .unwrap_or(AssertionOutcome::Verified),
            )
        }
        other => other,
    }
}

/// Typed single-assertion verification with encoding-phase panic protection.
///
/// Accepts typed obligations with direct TrustVcExpr access. No thread-local
/// lookup needed. Part of #2219. Migrated to TrustVcResult<AssertionOutcome>
/// as part of #1690.
pub(in crate::encoder) fn verify_single_assertion_typed(
    slices: &VerificationSlices<'_>,
    assertion: &crate::prepared_context::PreparedObligation,
    post_loop_modified_vars: Option<&HashSet<String>>,
) -> TrustVcResult<AssertionOutcome> {
    verify_single_assertion_typed_with_extra_variables(
        slices,
        assertion,
        post_loop_modified_vars,
        &[],
    )
}

pub(in crate::encoder) fn verify_single_assertion_typed_with_extra_variables(
    slices: &VerificationSlices<'_>,
    assertion: &crate::prepared_context::PreparedObligation,
    post_loop_modified_vars: Option<&HashSet<String>>,
    extra_variables: &[VariableDecl],
) -> TrustVcResult<AssertionOutcome> {
    // Clone the set so it can cross the catch_unwind boundary.
    let post_loop = post_loop_modified_vars.cloned();
    let extra_variables = extra_variables.to_vec();
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        verify_single_assertion_typed_inner(slices, assertion, post_loop.as_ref(), &extra_variables)
    }));
    match result {
        Ok(inner_result) => inner_result,
        Err(panic_info) => catch_encoding_panic_to_unknown(
            panic_info,
            "ay panic during encoding for",
            &assertion.name,
        ),
    }
}

struct MainAttemptResult {
    outcome: AssertionOutcome,
    effective_int_mode: bool,
}

// SharedBvFastPathAttempt, can_use_shared_bv_fast_path, and
// verify_assertion_with_shared_bv_encoder extracted to assertion_bv_reuse.rs (#2621).
pub(in crate::encoder) use super::assertion_bv_reuse::{
    can_use_shared_bv_fast_path, verify_assertion_with_shared_bv_encoder, SharedBvFastPathAttempt,
};

/// May the int-mode TIMEOUT retry (`verify_main_attempt_with_retries` step 1)
/// run for this assertion? Three conditions, each disqualifying on its own:
///
/// * the goal's own no-overflow predicates must have been CHECKED first
///   (`arith_overflow_enabled`); with no overflow the fixed-width and the
///   `Int` reading of the goal are the same statement, and without that check
///   they need not be;
/// * a `by(nonlinear_arith)` goal is ALREADY solved in the integers, so the
///   retry would be the identical query;
/// * every fact the solve holds must reach the `Int` reading UNCHANGED —
///   `arith_reading::every_fact_crosses_into`, which owns that reason (the
///   `Guarded` rewrite's guard is incomplete for a unary `-` that DOMINATES
///   the bounded node — a `-` sitting UNDER the bound is already covered, by
///   the homomorphism argument recorded there).
///
/// Named and unit-pinned rather than written inline at the call site: this
/// predicate can only ever suppress a TIMEOUT → `Verified` upgrade, so no
/// end-to-end fixture can distinguish it from `true` and without pins it is
/// code nothing measures.
fn int_fallback_allowed(
    slices: &VerificationSlices<'_>,
    is_nonlinear_arith: bool,
    arith_overflow_enabled: bool,
) -> bool {
    arith_overflow_enabled
        && !is_nonlinear_arith
        && super::arith_reading::every_fact_crosses_into(
            slices,
            super::arith_reading::ArithReading::MathInt,
        )
}

/// Run a single assertion attempt with the full timeout retry cascade.
///
/// 1. BV attempt (or forced timeout if test hook active)
/// 2. If timeout + `allow_int_fallback`: int-mode retry
/// 3. If still not recovered: extended-timeout retry in `initial_int_mode`
///
/// Returns both the final outcome and the int-mode that produced it,
/// so callers (including the confirmation check) can reuse the same mode.
/// Part of #2328.
fn verify_main_attempt_with_retries(
    slices: &VerificationSlices<'_>,
    assertion: &crate::prepared_context::PreparedObligation,
    initial_int_mode: bool,
    allow_int_fallback: bool,
    post_loop_modified_vars: Option<&HashSet<String>>,
    extra_variables: &[VariableDecl],
    cached_prune_plan: Option<&super::pruning::PrunePlan>,
) -> TrustVcResult<MainAttemptResult> {
    let ctx = slices.ctx;
    let owned_prune_plan;
    let prune_plan = if let Some(plan) = cached_prune_plan {
        plan
    } else {
        owned_prune_plan = super::pruning::build_per_assertion_prune_plan(slices, assertion);
        &owned_prune_plan
    };
    let encoder = match AYEncoder::setup_from_prepared_with_extra_variables_and_prune_plan(
        slices,
        initial_int_mode,
        post_loop_modified_vars,
        extra_variables,
        Some(assertion),
        Some(prune_plan),
    ) {
        Ok(enc) => enc,
        Err(err) => {
            return convert_setup_error(err).map(|outcome| MainAttemptResult {
                outcome,
                effective_int_mode: initial_int_mode,
            })
        }
    };

    let bv_outcome = if force_bv_timeout_enabled() {
        forced_timeout_result(&assertion.name)
    } else {
        verify_assertion_with_timeout_typed(encoder, assertion, ctx.rlimit_ms)?
    };

    let mut effective_int_mode = initial_int_mode;

    let outcome = match bv_outcome {
        AssertionOutcome::Unknown {
            ref reason,
            category,
            detail,
        } if category.unwrap_or_else(|| UnknownCategory::classify(reason))
            == UnknownCategory::Timeout =>
        {
            let orig = reason.clone();
            let orig_detail = detail;
            let mut recovered: Option<AssertionOutcome> = None;

            // Skip retry cascade when caller opts out (e.g. tests accepting
            // Unknown). Avoids ~30s of wasted encoder setup + solver timeout
            // per assertion. Part of #2707.
            if ctx.skip_retry_cascade {
                return Ok(MainAttemptResult {
                    outcome: AssertionOutcome::Unknown {
                        reason: orig,
                        category: Some(UnknownCategory::Timeout),
                        detail: orig_detail,
                    },
                    effective_int_mode,
                });
            }

            // Step 1: Int-mode retry (only if allowed). Part of #2262.
            if allow_int_fallback {
                recovered = AYEncoder::setup_from_prepared_with_extra_variables_and_prune_plan(
                    slices,
                    true,
                    post_loop_modified_vars,
                    extra_variables,
                    Some(assertion),
                    Some(prune_plan),
                )
                .map_err(|e| {
                    tracing::debug!(assertion = %assertion.name,
                        error = %format!("{e:?}"),
                        "Int-mode retry encoder setup failed");
                    e
                })
                .ok()
                .and_then(|e| {
                    verify_assertion_with_timeout_typed(e, assertion, ctx.rlimit_ms)
                        .map_err(|e| {
                            tracing::debug!(assertion = %assertion.name,
                                error = %format!("{e:?}"),
                                "Int-mode retry solver failed");
                            e
                        })
                        .ok()
                })
                .filter(|o| !matches!(o, AssertionOutcome::Unknown { .. }));
                if recovered.is_some() {
                    effective_int_mode = true;
                    tracing::info!(assertion = %assertion.name,
                        outcome = ?recovered,
                        "BV timeout recovered via integer-mode retry");
                }
            }

            // Step 2: Extended-timeout retry (if int-mode didn't recover). Part of #2313.
            if recovered.is_none() {
                if force_extended_retry_success_enabled() {
                    recovered = Some(AssertionOutcome::Verified);
                    tracing::info!(assertion = %assertion.name,
                        "Timeout recovered via extended-timeout retry (forced)");
                } else {
                    recovered = AYEncoder::setup_from_prepared_with_extra_variables_and_prune_plan(
                        slices,
                        initial_int_mode,
                        post_loop_modified_vars,
                        extra_variables,
                        Some(assertion),
                        Some(prune_plan),
                    )
                    .map_err(|e| {
                        tracing::debug!(assertion = %assertion.name,
                            error = %format!("{e:?}"),
                            "Extended-timeout retry encoder setup failed");
                        e
                    })
                    .ok()
                    .and_then(|e| {
                        verify_assertion_with_timeout_typed_extended(e, assertion, ctx.rlimit_ms)
                            .map_err(|e| {
                                tracing::debug!(assertion = %assertion.name,
                                    error = %format!("{e:?}"),
                                    "Extended-timeout retry solver failed");
                                e
                            })
                            .ok()
                    })
                    .filter(|o| !matches!(o, AssertionOutcome::Unknown { .. }));
                    if recovered.is_some() {
                        tracing::info!(assertion = %assertion.name,
                            outcome = ?recovered,
                            "Timeout recovered via extended-timeout retry");
                    }
                }
            }

            recovered.unwrap_or(AssertionOutcome::Unknown {
                reason: orig,
                category: Some(UnknownCategory::Timeout),
                detail: orig_detail,
            })
        }
        other => other,
    };

    Ok(MainAttemptResult {
        outcome,
        effective_int_mode,
    })
}

pub(super) fn apply_collection_confirmation(
    slices: &VerificationSlices<'_>,
    assertion: &crate::prepared_context::PreparedObligation,
    outcome: AssertionOutcome,
    effective_int_mode: bool,
    post_loop_modified_vars: Option<&HashSet<String>>,
    extra_variables: &[VariableDecl],
    cached_prune_plan: Option<&super::pruning::PrunePlan>,
) -> TrustVcResult<AssertionOutcome> {
    let ctx = slices.ctx;
    if !matches!(&outcome, AssertionOutcome::Verified)
        || !(assertion.expr.references_collection() || ctx.has_collection_context)
    {
        return Ok(outcome);
    }

    // Slice 3 of #2706: a strict UNSAT proof certificate is a stronger
    // determinism guarantee than a second solver run.  Skip the
    // confirmation re-check when one is available.
    #[cfg(feature = "proof-certificates")]
    if crate::verification_report::current_proof_is_strict(&assertion.name) {
        tracing::debug!(
            assertion = %assertion.name,
            "skipping collection confirmation — strict proof certificate available"
        );
        return Ok(outcome);
    }

    #[cfg(test)]
    if super::test_hooks::FORCE_CONFIRMATION_DISAGREE.with(|f| f.get()) {
        crate::verification_report::record_used_assumptions(&[]);
        return Ok(AssertionOutcome::Unknown {
            reason: format!(
                "Confirmation check disagreed for '{}' — \
                 possible ay-dpll non-determinism (#2241)",
                assertion.name
            ),
            category: Some(UnknownCategory::ConfirmationDisagree),
            detail: None,
        });
    }

    let confirm_result = verify_main_attempt_with_retries(
        slices,
        assertion,
        effective_int_mode,
        // The fourth copy of the same predicate, now reading the one gate. The
        // `!effective_int_mode` conjunct is this site's own (an int-mode run has
        // no BV overflow to fall back from); the rest is
        // `exec_arith_overflow_in_scope`.
        exec_arith_overflow_in_scope(ctx.check_overflow() && !effective_int_mode, assertion),
        post_loop_modified_vars,
        extra_variables,
        cached_prune_plan,
    )?;
    Ok(match confirm_result.outcome {
        AssertionOutcome::Verified => outcome,
        // FAIL CLOSED, and SAY WHAT HAPPENED. The primary attempt is not
        // republished: whatever the confirmation returned, this obligation
        // does not come back `Verified`. What changed 2026-09-15 is the
        // message. This arm used to assert "possible ay-dpll non-determinism
        // (#2241)" and throw the confirmation's own outcome away
        // (`detail: None`), so a confirmation that merely TIMED OUT, or whose
        // correct UNSAT ay refused to publish because the certification
        // envelope had expired, was reported as a solver disagreeing with
        // itself. That is how a deadline skew (see
        // `verification::timeout::DEFAULT_SOLVER_WALL_BACKSTOP_MS`) spent a
        // day looking like a non-determinism bug. The category stays
        // `ConfirmationDisagree` — it is the one fact this site actually
        // knows, "the second solve did not confirm" — and the confirmation's
        // real outcome now travels with it.
        confirm => {
            crate::verification_report::record_used_assumptions(&[]);
            AssertionOutcome::Unknown {
                reason: format!(
                    "Confirmation check disagreed for '{}': the re-solve \
                     returned {}. Fail-closed — the primary `Verified` is not \
                     published. A re-solve that does not confirm can be a \
                     genuine solver disagreement (ay #2241), a timeout, or ay \
                     declining to publish a computed result whose envelope \
                     expired; read the outcome above before attributing it",
                    assertion.name,
                    describe_confirmation_outcome(&confirm),
                ),
                category: Some(UnknownCategory::ConfirmationDisagree),
                detail: None,
            }
        }
    })
}

/// One-line rendering of what a confirmation re-solve actually returned, for
/// the message above. Deliberately includes ay's own unknown reason when there
/// is one: that string is what distinguishes "solver disagreed", "timeout" and
/// "certification declined to publish".
fn describe_confirmation_outcome(outcome: &AssertionOutcome) -> String {
    match outcome {
        AssertionOutcome::Verified => "Verified".to_string(),
        AssertionOutcome::Counterexample { .. } => "a Counterexample".to_string(),
        AssertionOutcome::Error { message } => format!("Error ({message})"),
        AssertionOutcome::Unknown {
            reason,
            category,
            detail,
        } => {
            let category = category
                .map(|c| format!("{c:?}"))
                .unwrap_or_else(|| "Unknown".to_string());
            match detail {
                Some(detail) => format!("Unknown/{category} ({reason}; ay detail: {detail:?})"),
                None => format!("Unknown/{category} ({reason})"),
            }
        }
    }
}

/// Dispatch gate for the nonlinear-real certificate pre-pass.
///
/// Returns `true` **only** when the obligation carries an explicit
/// `by(nonlinear_arith)` hint (`SolverMode::NonlinearArith`). This is the
/// soundness-critical boundary that distinguishes upstream `real_nonlinear1`
/// (which carries the hint and is discharged by the certificate search) from
/// `real_nonlinear2` (the *same* goal with **no** hint, which Verus expects to
/// FAIL): every non-`NonlinearArith` mode — including the default `None` — must
/// keep the NRA pre-pass switched off so a hint-free goal falls through to the
/// ordinary solver. A leak here would silently prove `real_nonlinear2` and
/// diverge from Verus.
pub(super) fn is_nonlinear_arith_mode(mode: Option<crate::vc::SolverMode>) -> bool {
    mode.is_some_and(|m| m == crate::vc::SolverMode::NonlinearArith)
}

/// Does this obligation carry Verus SPEC arithmetic (mathematical `int`, no
/// overflow) rather than exec arithmetic?
///
/// The exec-arith overflow checks (#2778) are emitted from EACH obligation's
/// expression (see `body_extract::maybe_emit_exec_arith_overflow_check`), which
/// makes them wrongly fire on SPEC-predicate obligations whose arithmetic is
/// spec, not exec: a `calc!` step (carries `step_meta`), a call-site precondition
/// check (`__call_requires_*`), or a contract requires/ensures/recommends clause.
/// In Verus these are mathematical-`int` and are NEVER overflow-checked. Genuine
/// EXEC arithmetic safety still flows through the body-extract `overflow_check_*`
/// obligations (plain `Assert`s with no `step_meta`/contract kind), which this
/// predicate excludes. Without this gate a `requires(x + y == z)` / `calc!`
/// spuriously fails on `x = y = MAX` (regression surfaced once the cargo fixtures
/// were relockable: `cargo_vstd_macro_usage::calc_test`/`do_something`).
pub(super) fn obligation_carries_spec_arithmetic(
    assertion: &crate::prepared_context::PreparedObligation,
) -> bool {
    assertion.step_meta.is_some()
        || assertion.name.starts_with("__call_requires_")
        || matches!(
            assertion.kind,
            ObligationKind::Requires
                | ObligationKind::Ensures
                | ObligationKind::LoopEnsures
                | ObligationKind::Recommends
        )
}

/// THE ONE GATE for this obligation's exec-arith no-overflow predicates.
///
/// SOUNDNESS-CRITICAL, and it exists because the two halves DISAGREED.
/// `verify_assertion_typed` (`solve.rs`) re-encodes the goal's own no-overflow
/// predicates and ASSERTS them into the solver — the "Assert+Assume" pattern
/// (#2516) — on the strength of a comment that says they "were already verified
/// in a separate encoder". They were verified only when the CHECK ran, and the
/// check is deliberately suppressed for three families:
///
/// * `by(bit_vector)` — the assertion is bit-vector math, which WRAPS, so there
///   is no no-overflow property to rely on and none is checked;
/// * `by(nonlinear_arith)` — solved in the integers, where the `+`/`-`/`*`
///   no-overflow predicates are not emitted at all (`encode_int_arith` takes
///   `wrap_ctx = None` under `use_int_arithmetic`) and the CHECK that would
///   justify assuming any of the rest is skipped outright by the separate
///   `!is_nonlinear_arith &&` guard on the check-emitting block below. NOT a
///   vacuous conjunct: the `Div`/`Rem` arms and the collection encoders still
///   push predicates in that lane, so without this row the assume site would
///   assert an unproven `b != 0`. Pinned by
///   `the_exec_arith_overflow_gate_is_closed_for_a_nonlinear_arith_goal` and
///   its non-vacuity twin;
/// * spec-predicate obligations ([`obligation_carries_spec_arithmetic`]) —
///   mathematical `int` in Verus, never overflow-checked.
///
/// For exactly those obligations the assume site was injecting an UNPROVEN and,
/// at the witness point, FALSE fact. With `y: u32` pinned to `u32::MAX`, the
/// assumed `y + 1 <= u32::MAX` contradicts the hypothesis, and EVERY goal that
/// mentions `y + 1u32` becomes vacuously true — measured:
/// `assert_by_bit_vector!(y + 1u32 == 7u32)` VERIFIED, and a caller-side
/// `requires(z + 1u32 == 0u32 && 1u32 == 2u32)` VERIFIED. The check site and the
/// assume site now read the SAME predicate, so "assume only what was checked"
/// is a structural property rather than a convention two files have to keep.
pub(in crate::encoder) fn exec_arith_overflow_in_scope(
    context_checks_overflow: bool,
    assertion: &crate::prepared_context::PreparedObligation,
) -> bool {
    context_checks_overflow
        && !matches!(
            assertion.solver_mode,
            Some(crate::vc::SolverMode::BitVector)
        )
        && !is_nonlinear_arith_mode(assertion.solver_mode)
        && !obligation_carries_spec_arithmetic(assertion)
}

/// Inner typed single-assertion verification.
fn verify_single_assertion_typed_inner(
    slices: &VerificationSlices<'_>,
    assertion: &crate::prepared_context::PreparedObligation,
    post_loop_modified_vars: Option<&HashSet<String>>,
    extra_variables: &[VariableDecl],
) -> TrustVcResult<AssertionOutcome> {
    // Quantifier-conjunction soundness (round-4 quantifiers finding). A
    // TRIGGERLESS `forall|x| (C₁ ∧ C₂ ∧ …)` whose body conjunction contains a
    // nested quantifier refutes (in the single-solve path) to a mixed
    // (quantified-disjunct ∨ ground-disjunct) goal that ay decides UNSOUNDLY
    // (spurious UNSAT → false-`Verified`). Verify each conjunct's universal as a
    // SEPARATE query instead — exact distribution `∀x.(A∧B) ⟺ (∀x.A)∧(∀x.B)` —
    // so every sub-query is a pure quantifier OR pure ground refutation, never the
    // mixed shape. Sound and (for independent conjuncts) complete; falls through
    // (`None`) for every other assertion, leaving all other paths unchanged.
    if let Some(outcome) = super::split::try_verify_quantified_conjunction_split(
        slices,
        assertion,
        post_loop_modified_vars,
    )? {
        return Ok(outcome);
    }

    let ctx = slices.ctx;
    let mut assertion_prune_plan =
        super::pruning::build_per_assertion_prune_plan(slices, assertion);
    // NonlinearArith mode: all variables as Sort::Int so ay's integer theory
    // handles *, /, % symbolically. No BV wrapping, no overflow. Part of #2187.
    let is_nonlinear_arith = is_nonlinear_arith_mode(assertion.solver_mode);

    // Sound nonlinear-real certificate pre-pass (degree-2 polynomial
    // implications over reals via Positivstellensatz-style certificate search).
    // Only runs under an explicit `by(nonlinear_arith)` hint and only ever
    // *upgrades* to Verified when a certificate is found — otherwise it falls
    // through to the ordinary solver (fail-closed). This discharges the
    // `real_nonlinear1` division-shape lemma that the integer-theory solver
    // cannot, while leaving the hint-free `real_nonlinear2` to fail normally.
    if is_nonlinear_arith {
        if let Some(verified) =
            super::nonlinear_real::try_prove_nonlinear_real_outcome(&assertion.expr)
        {
            tracing::info!(
                assertion = %assertion.name,
                "nonlinear-real certificate search discharged by(nonlinear_arith) goal"
            );
            return Ok(verified);
        }
    }

    // Verus-faithful DEFAULT-prover boundary (the `smt.arith.nl=false` analog).
    //
    // Verus's default queries deliberately exclude nonlinear arithmetic —
    // nonlinear real reasoning requires an explicit `by(nonlinear_arith)`
    // hint, and upstream tests (real.rs `real_nonlinear2`) ENCODE that a true
    // nonlinear-real fact must FAIL hint-free. Since ay's NRA interval
    // branch-and-prune lane (ay 43034c4b0c) the bare solver can decide such
    // facts, so without this boundary an unhinted goal would silently verify
    // and diverge from Verus (the exact leak the `is_nonlinear_arith_mode`
    // doc-comment warns about, arriving via ay instead of the pre-pass).
    // A hint-free real-nonlinear goal is therefore refused up front and
    // classified as genuine theory INCOMPLETENESS: the gate mapper surfaces
    // that as a model-less verification failure (upstream
    // `Invalid(None, None, None)` / `assert_one_fails`), never a fabricated
    // model, never `Verified` (design-unknown-as-failure.md). Sound in
    // both directions: refusing to prove is always conservative, and the
    // hinted path (pre-pass above + NonlinearArith mode) keeps the full
    // proving power exactly like Verus's dedicated nonlinear query.
    if matches!(
        assertion.solver_mode,
        None | Some(crate::vc::SolverMode::Default)
    ) {
        if let Some(construct) =
            super::nonlinear_real::unhinted_nonlinear_real_construct(&assertion.expr)
        {
            tracing::info!(
                assertion = %assertion.name,
                construct,
                "refusing hint-free nonlinear-real goal on the default prover \
                 profile (Verus smt.arith.nl=false analog)"
            );
            return Ok(AssertionOutcome::unknown(
                format!(
                    "goal contains {construct}: nonlinear real arithmetic is outside \
                     the default prover profile (Verus-faithful `smt.arith.nl=false` \
                     analog) and requires `by(nonlinear_arith)` \
                     (`trust_vc::assert_by_nonlinear!`)"
                ),
                Some(UnknownCategory::Incompleteness),
            ));
        }

        // NOTE (deliberate asymmetry with the REAL boundary above): hint-free
        // MATH-int (`int`/`nat`) nonlinear goals are NOT refused. Unlike
        // `real` (where upstream real.rs `real_nonlinear2` PINS the hint-free
        // failure), the default-lane int NIA capability is a deliberate,
        // test-pinned trust-vc superset: the `nia_zero_bound_products`,
        // `arithmetic_normalization` gcd/commutativity, and
        // `regression_math_int` families all verify (or refute) hint-free
        // int products on this path, and no upstream expected-fail case
        // flips. The ay NIA SOS/Positivstellensatz UNSAT pre-phase
        // (ay a084749365, gated by e05b2c007e) extends this to true
        // quadratic-form facts — audited sound (UNSAT-only; adversarial
        // negatives stay unverified, see
        // `int_var_times_var_perfect_square_verifies_via_sos`).
    }

    // BitVector mode (`assert by(bit_vector)`): the expression is interpreted
    // with wrapping bit-vector semantics, so arithmetic carries no overflow
    // obligation (matches Verus). Collection-precondition checks still run.
    // The SAME gate decides whether `solve.rs` may ASSUME those predicates —
    // see `exec_arith_overflow_in_scope`.
    let arith_overflow_enabled = exec_arith_overflow_in_scope(ctx.check_overflow(), assertion);

    let use_int_for_measures = is_nonlinear_arith
        || matches!(
            assertion.kind,
            ObligationKind::MeasureNonNegative | ObligationKind::MeasureDecreases
        );
    let mut run_diagnostics = EncodingDiagnostics::default();

    // Overflow checking: use a SEPARATE encoder to avoid corrupting the main
    // encoder's ay-dpll solver state. Push/pop from overflow checks puts the
    // solver into incremental mode with retained Tseitin state. Fixes
    // regression from fd05e3aa.
    //
    // Skip for NonlinearArith: math integers have no overflow. Part of #2187.
    if !is_nonlinear_arith
        && assertion
            .expr
            .may_emit_overflow_checks(arith_overflow_enabled)
    {
        // OBLIGATION-LOCAL PRUNE (the collection-precondition / overflow lane).
        //
        // These predicates — `Seq::subrange(start, end) requires end <= len`,
        // `requires 0 <= i < len`, the carrier-index representability bound,
        // the arithmetic no-overflow atoms — are LENGTH and SCALAR claims. The
        // Seq ELEMENT model (the `__seq_shifted`/`__seq_concat` defining
        // `forall`s, their ground `select` instances and the `bv2nat` length
        // companions that carry them) is unreachable from all of them, yet the
        // whole-query analysis has to keep it whenever ANY obligation in the
        // unit reads an element — which is exactly when the lane drowns: a
        // `2 <= 3` bound arrives at ay wrapped in AUFBV with `int2bv`, and ay
        // computes UNSAT but cannot certify it, publishing
        // `unknown (incomplete self-check-rejected)`.
        //
        // This lane already builds its OWN encoder, so it can simply be built
        // in the weaker element-free context and consulted first.
        //
        // SOUNDNESS. Entailment is monotone: the pruned context is a strict
        // SUBSET of the full context's assertions (pruning drops assertions
        // only — `encode_index_shifted_seq` re-pushes its representability
        // obligation on the pruned path so the OBLIGATION set is unchanged), so
        // anything the pruned context proves the full context proves too. Only
        // `Verified` is accepted from it; every other outcome — Counterexample,
        // Unknown, a setup error — is DISCARDED and the full-context lane runs
        // unchanged, so no rejection and no counterexample is ever read off the
        // weaker context.
        let mut pruned_overflow_outcome = None;
        if matches!(
            assertion_prune_plan.element_demand(),
            super::pruning::ElementDemand::Observed
        ) {
            assertion_prune_plan.set_element_demand(super::pruning::ElementDemand::LengthOnly);
            let pruned_setup = AYEncoder::setup_overflow_from_prepared(
                slices,
                assertion,
                use_int_for_measures,
                post_loop_modified_vars,
                extra_variables,
                Some(assertion),
                Some(&assertion_prune_plan),
            );
            assertion_prune_plan.set_element_demand(super::pruning::ElementDemand::Observed);
            if let Ok(mut pruned_encoder) = pruned_setup {
                if let Ok(outcome) = check_overflow_predicates(
                    &mut pruned_encoder,
                    assertion,
                    arith_overflow_enabled,
                ) {
                    if matches!(outcome, AssertionOutcome::Verified) {
                        run_diagnostics.merge(&pruned_encoder.state.diagnostics);
                        pruned_overflow_outcome = Some(outcome);
                    }
                }
            }
        }

        if pruned_overflow_outcome.is_none() {
            let mut overflow_encoder = match AYEncoder::setup_overflow_from_prepared(
                slices,
                assertion,
                use_int_for_measures,
                post_loop_modified_vars,
                extra_variables,
                Some(assertion),
                Some(&assertion_prune_plan),
            ) {
                Ok(enc) => enc,
                Err(err) => return convert_setup_error(err),
            };
            let overflow_outcome = check_overflow_predicates(
                &mut overflow_encoder,
                assertion,
                arith_overflow_enabled,
            )?;
            run_diagnostics.merge(&overflow_encoder.state.diagnostics);
            if !matches!(overflow_outcome, AssertionOutcome::Verified) {
                return Ok(overflow_outcome);
            }
        }
    }

    // Main assertion: fresh encoder with clean solver state and full timeout
    // retry cascade (int-mode fallback + extended-timeout retry). Part of #2328.
    // NonlinearArith starts in int_mode, so int-mode fallback is redundant.
    let MainAttemptResult {
        mut outcome,
        effective_int_mode,
    } = verify_main_attempt_with_retries(
        slices,
        assertion,
        use_int_for_measures,
        int_fallback_allowed(slices, is_nonlinear_arith, arith_overflow_enabled),
        post_loop_modified_vars,
        extra_variables,
        Some(&assertion_prune_plan),
    )?;

    // Demand-inline retry: if baseline failed, try inlining body axioms for
    // callees referenced in the assertion. Upgrades failure → Verified, and
    // resolves a fail-closed Unknown → model-validated Counterexample (the
    // definitional-unfolding CE direction; see maybe_retry_with_demand_inlining).
    // Part of #2655.
    let mut via_demand_inline = false;
    if !matches!(outcome, AssertionOutcome::Verified) {
        if let Some(recovered) = maybe_retry_with_demand_inlining(
            slices,
            assertion,
            &outcome,
            use_int_for_measures,
            post_loop_modified_vars,
            extra_variables,
            Some(&assertion_prune_plan),
        )? {
            outcome = recovered;
            via_demand_inline = true;
        }
    }

    // Adaptive E-matching escalation: if the outcome is Unknown due to
    // quantifier round budget exhaustion, retry with escalated limits.
    // Only attempts escalation when skip_retry_cascade is false and the
    // Unknown detail is budget-retriable (#2720).
    let mut via_ematching_escalation = false;
    if !matches!(outcome, AssertionOutcome::Verified) && !ctx.skip_retry_cascade {
        if let Some(recovered) = maybe_retry_with_ematching_escalation(
            slices,
            assertion,
            &outcome,
            use_int_for_measures,
            post_loop_modified_vars,
            extra_variables,
            Some(&assertion_prune_plan),
        )? {
            outcome = recovered;
            via_ematching_escalation = true;
        }
    }

    // Skip collection confirmation when the proof was recovered via
    // demand-inline or E-matching escalation (#2687, #2720). These retries
    // change the solver configuration, so disagreement is expected and
    // deterministic — not ay-dpll non-determinism.
    let outcome = if via_demand_inline || via_ematching_escalation {
        outcome
    } else {
        apply_collection_confirmation(
            slices,
            assertion,
            outcome,
            effective_int_mode,
            post_loop_modified_vars,
            extra_variables,
            Some(&assertion_prune_plan),
        )?
    };

    Ok(demote_verified_outcome(
        outcome,
        &assertion.name,
        &run_diagnostics,
    ))
}

/// Decides whether a shared-BV fast-path outcome should fall back to the
/// per-assertion path so the demand-inline retry can run.
///
/// The shared-BV fast path is a single bare solve with no retry cascade; a
/// fail-closed `Unknown` produced there would otherwise be terminal even when
/// inlining a callee's defining body decides the query (in either direction —
/// the missed `Verified` upgrade and the missed definitional-unfolding
/// `Counterexample`, e.g. upstream basic.rs `test_spec_fn`). Fall back exactly
/// when the retry has something to try: the outcome is `Unknown`, demand
/// inlining is enabled, and at least one visible (non-opaque/hidden-unrevealed,
/// non-recursive) callee body is selectable from the active query. Pure
/// catalog/selection work — no solver calls — so the check is cheap; the
/// fallback then re-verifies with the full cascade. Fail-closed: when the
/// retry does not improve the result, the fallback reproduces the same
/// baseline `Unknown`. Part of #2655.
fn select_demand_inline_candidates_for_query(
    slices: &VerificationSlices<'_>,
    assertion: &PreparedObligation,
    catalog: &std::collections::HashMap<String, super::body_support::ExtractedBodyAxiom>,
    depth_bound: usize,
    max_callees: usize,
) -> super::body_support::DemandInlineSelection {
    let supporting_exprs = slices
        .assumptions
        .iter()
        .chain(slices.verified_invariants)
        .chain(slices.verified_assert_by)
        .chain(slices.scoped_assumptions)
        .map(|obligation| &obligation.expr)
        .collect::<Vec<_>>();

    super::body_support::select_demand_inline_candidates(
        &assertion.expr,
        &supporting_exprs,
        catalog,
        depth_bound,
        max_callees,
    )
}

/// Whether a demand-inline retry is an exact enough transformation to adopt a
/// SAT result as a counterexample to the ORIGINAL query.
///
/// `Verified` is safe even after bounded/truncated expansion because removing a
/// defining axiom only weakens the assumptions and makes proof harder. A model
/// is asymmetric: if a selected call survives the depth bound, that model may
/// assign the residual UF a value incompatible with the dropped definition.
/// Therefore Counterexample adoption requires (1) proof provenance for every
/// recursive SCC selected and (2) complete elimination of selected calls from
/// every expression the retry encodes. Dead arms pruned by exact static branch
/// selection do not count as residuals.
fn demand_inline_counterexample_retry_is_exact(
    slices: &VerificationSlices<'_>,
    assertion: &PreparedObligation,
    catalog: &std::collections::HashMap<String, super::body_support::ExtractedBodyAxiom>,
    candidates: &[String],
) -> bool {
    if !super::body_support::selected_recursive_cycles_are_admitted(
        catalog,
        candidates,
        &slices.ctx.source_catalog_admitted_definitions,
    ) {
        return false;
    }

    let selected: HashSet<&str> = candidates.iter().map(String::as_str).collect();
    let mut inline_bodies = std::collections::HashMap::new();

    // Mirror setup.rs's ordinary inline catalog first. Hidden inline functions
    // are absent unless revealed; inline+opaque is rejected at extraction.
    for broadcast in slices.broadcast_assumptions {
        let Some(body) = super::body_support::extracted_inline_body_axiom(broadcast) else {
            continue;
        };
        if super::body_support::fn_name_named_in(&body.function_name, &slices.ctx.hidden_fns)
            && !super::body_support::fn_name_named_in(&body.function_name, &slices.ctx.revealed_fns)
        {
            continue;
        }
        inline_bodies.insert(
            body.function_name,
            (body.param_names, body.param_types, body.body),
        );
    }
    // Then mirror the attempt-local demand-inline overrides.
    for name in candidates {
        let Some(body) = catalog.get(name) else {
            return false;
        };
        inline_bodies.insert(
            body.function_name.clone(),
            (
                body.param_names.clone(),
                body.param_types.clone(),
                body.body.clone(),
            ),
        );
    }

    let has_residual = |expr: &TrustVcExpr| {
        let expanded = crate::encoder::eval::substitute_inline_calls(expr, &inline_bodies);
        super::body_support::referenced_function_names(&expanded)
            .iter()
            .any(|name| selected.contains(name.as_str()))
    };

    if has_residual(&assertion.expr)
        || slices
            .assumptions
            .iter()
            .chain(slices.verified_invariants)
            .chain(slices.verified_assert_by)
            .chain(slices.scoped_assumptions)
            .any(|obligation| has_residual(&obligation.expr))
    {
        return false;
    }

    // Candidate and ordinary-inline body axioms are omitted by setup; every
    // other broadcast remains live and must also be completely transformed.
    slices.broadcast_assumptions.iter().all(|broadcast| {
        let extracted = super::body_support::extracted_body_axiom(broadcast);
        let omitted = broadcast.is_inline
            || extracted
                .as_ref()
                .is_some_and(|body| selected.contains(body.function_name.as_str()));
        omitted
            || (!has_residual(&broadcast.expr)
                && broadcast
                    .broadcast_guard
                    .as_ref()
                    .is_none_or(|guard| !has_residual(guard)))
    })
}

pub(super) fn unknown_should_fall_back_to_demand_inline(
    slices: &VerificationSlices<'_>,
    assertion: &crate::prepared_context::PreparedObligation,
    outcome: &AssertionOutcome,
) -> bool {
    if !matches!(outcome, AssertionOutcome::Unknown { .. }) {
        return false;
    }
    let ctx = slices.ctx;
    let config = ctx.demand_inline;
    if !config.enabled() || config.depth_bound() == 0 {
        return false;
    }
    let primary_fn = ctx.function_context.as_ref().map(|fc| fc.name.as_str());
    let catalog = super::body_support::build_body_catalog(
        slices.broadcast_assumptions,
        primary_fn,
        &ctx.revealed_fns,
        &ctx.hidden_fns,
    );
    if catalog.is_empty() {
        return false;
    }
    !select_demand_inline_candidates_for_query(
        slices,
        assertion,
        &catalog,
        config.depth_bound(),
        config.max_callees(),
    )
    .functions
    .is_empty()
}

/// Attempt demand-driven inlining retry for a failed assertion.
///
/// Returns `Some(Verified)` if inlining body axioms recovers the proof, and
/// `Some(Counterexample)` when the BASELINE outcome was a fail-closed
/// `Unknown` and the inline-substituted retry produces a model-validated
/// refutation. Returns `None` if the retry is skipped or does not improve
/// the result.
///
/// SOUNDNESS of the Counterexample direction: the retry re-encodes the SAME
/// query with the candidates' defining bodies substituted at every call site
/// (`substitute_inline_calls` runs inside `encode_condition_typed`, so every
/// assumption, broadcast, and the goal see the substitution), which for a
/// total, non-recursive definitional body is an exact, equisatisfiable
/// transformation. `build_body_catalog` excludes direct self-recursion and
/// unrevealed opaque/hidden bodies; admitted mutual recursion is accepted only
/// when static branch selection eliminates every selected call and the source
/// catalog carries checked termination provenance for the whole SCC. A
/// `Counterexample` outcome from
/// the retry has already passed ay's own model validation
/// (`sat_model_validated`, solve.rs) plus trust-vc's broadcast-premise
/// revalidation, so it is a genuine countermodel of the original obligation.
/// Adoption is restricted to a baseline `Unknown` (never `Error`, and a
/// baseline model-bearing `Counterexample` is kept as-is): it converts a
/// fail-closed non-verdict into the definitive refutation Verus reports for
/// the same program (upstream `assert_one_fails`), and can never manufacture
/// a `Verified` — the cardinal proves-more-than-Verus direction is untouched.
/// This closes the revealed-opaque/nested-spec-fn CE class (basic.rs
/// `test_spec_fn`): ay fail-closes SAT finalization on a two-level
/// definitional forall chain (`quantifier-ematching-exists`), while the
/// inlined retry query is ground and decides. Part of #2655.
fn maybe_retry_with_demand_inlining(
    slices: &VerificationSlices<'_>,
    assertion: &crate::prepared_context::PreparedObligation,
    baseline_outcome: &AssertionOutcome,
    use_int_for_measures: bool,
    post_loop_modified_vars: Option<&HashSet<String>>,
    extra_variables: &[VariableDecl],
    cached_prune_plan: Option<&super::pruning::PrunePlan>,
) -> TrustVcResult<Option<AssertionOutcome>> {
    let ctx = slices.ctx;
    let config = ctx.demand_inline;
    if !config.enabled() || config.depth_bound() == 0 {
        return Ok(None);
    }

    let primary_fn = ctx.function_context.as_ref().map(|fc| fc.name.as_str());
    let catalog = super::body_support::build_body_catalog(
        slices.broadcast_assumptions,
        primary_fn,
        &ctx.revealed_fns,
        &ctx.hidden_fns,
    );
    if catalog.is_empty() {
        return Ok(None);
    }

    let selection = select_demand_inline_candidates_for_query(
        slices,
        assertion,
        &catalog,
        config.depth_bound(),
        config.max_callees(),
    );
    let candidates = selection.functions;
    if candidates.is_empty() {
        return Ok(None);
    }

    let counterexample_retry_is_exact =
        demand_inline_counterexample_retry_is_exact(slices, assertion, &catalog, &candidates);

    tracing::info!(
        assertion = %assertion.name,
        candidates = ?candidates,
        "Attempting demand-inline retry (#2655)",
    );

    let encoder = AYEncoder::setup_from_prepared_with_inline_overrides_and_prune_plan(
        slices,
        use_int_for_measures,
        post_loop_modified_vars,
        extra_variables,
        Some(assertion),
        &candidates,
        cached_prune_plan,
    );

    let encoder = match encoder {
        Ok(enc) => enc,
        Err(err) => {
            tracing::debug!(
                assertion = %assertion.name,
                error = %format!("{err:?}"),
                "Demand-inline retry encoder setup failed"
            );
            return Ok(None);
        }
    };

    let retry_outcome = super::assertion_timeout::verify_assertion_with_timeout_typed(
        encoder,
        assertion,
        ctx.rlimit_ms,
    )?;

    match retry_outcome {
        AssertionOutcome::Verified => {
            crate::verification_report::record_demand_inline_recovery(
                &candidates,
                selection.depth_used,
            );
            tracing::info!(
                assertion = %assertion.name,
                inlined = ?candidates,
                "Demand-inline retry succeeded — consider strengthening callee contracts (#2655)",
            );
            Ok(Some(AssertionOutcome::Verified))
        }
        AssertionOutcome::Counterexample { .. }
            if counterexample_retry_is_exact
                && matches!(baseline_outcome, AssertionOutcome::Unknown { .. }) =>
        {
            // Definitional-unfolding refutation: the baseline was a
            // fail-closed Unknown; the exact inlined query produced a
            // model-validated countermodel (see fn doc-comment for the
            // soundness argument). Adopt it so the verdict class matches
            // Verus's assertion failure instead of a model-less Unknown.
            tracing::info!(
                assertion = %assertion.name,
                inlined = ?candidates,
                "Demand-inline retry resolved a fail-closed Unknown to a \
                 model-validated Counterexample (#2655)",
            );
            Ok(Some(retry_outcome))
        }
        _ => {
            tracing::debug!(
                assertion = %assertion.name,
                outcome = ?retry_outcome,
                counterexample_retry_is_exact,
                "Demand-inline retry did not improve result",
            );
            Ok(None)
        }
    }
}

/// E-matching round limits for adaptive escalation (#2720).
///
/// Start at the ay-dpll default (8), then escalate through these budgets.
/// Each step doubles the prior limit. Capped at 32 to bound worst-case
/// solver time.
const EMATCHING_ESCALATION_BUDGETS: &[usize] = &[16, 32];

/// Attempt adaptive E-matching escalation for a budget-retriable Unknown.
///
/// When the solver reports `QuantifierRoundLimit` or `QuantifierDeferred`,
/// the E-matching round budget was exhausted before instantiation converged.
/// Retry with progressively larger budgets (16, 32). Returns `Some(Verified)`
/// if escalation recovers the proof, `None` otherwise.
///
/// Solver recycling (#2742): the encoder is set up once and reused across
/// budget levels via push/pop (the internal mechanism of
/// `verify_assertion_with_timeout_reuse`). Only falls back to a fresh
/// encoder when the previous one was consumed by timeout or panic.
/// Part of #2720, #2742.
fn maybe_retry_with_ematching_escalation(
    slices: &VerificationSlices<'_>,
    assertion: &crate::prepared_context::PreparedObligation,
    current_outcome: &AssertionOutcome,
    use_int_for_measures: bool,
    post_loop_modified_vars: Option<&HashSet<String>>,
    extra_variables: &[VariableDecl],
    cached_prune_plan: Option<&super::pruning::PrunePlan>,
) -> TrustVcResult<Option<AssertionOutcome>> {
    let detail = match current_outcome {
        AssertionOutcome::Unknown { detail, .. } => *detail,
        _ => return Ok(None),
    };
    let Some(detail) = detail else {
        return Ok(None);
    };
    if !detail.is_budget_retriable() {
        return Ok(None);
    }

    let ctx = slices.ctx;

    // Solver recycling: set up the encoder once and carry it across budget
    // levels. If the solver times out or panics the encoder is lost, so we
    // fall back to a fresh setup for the next level. Part of #2742.
    let mut recycled_encoder: Option<AYEncoder> = None;

    for &budget in EMATCHING_ESCALATION_BUDGETS {
        tracing::info!(
            assertion = %assertion.name,
            ematching_rounds = budget,
            recycled = recycled_encoder.is_some(),
            "Attempting E-matching escalation retry (#2720, #2742)",
        );

        let encoder = if let Some(mut enc) = recycled_encoder.take() {
            // Reuse the encoder from the previous budget level. Reset ground
            // pool flush state so axioms are re-emitted after try_pop()
            // retracted the previous assertion's scoped assertions. Part of #2742.
            enc.state.ground_pool.reset_flush_state();
            // Drop memoized nat-cast lowerings: their floor/invalid skolem
            // bounds were asserted inside the popped scope, so re-encoding must
            // mint and re-constrain fresh skolems. Reusing a popped alias would
            // leave the floor unconstrained (unsound). Fail-closed: clearing only
            // forfeits memoization, never reuses a stale term.
            enc.state.nat_cast_aliases.clear();
            // Drop memoized map-dom bridges and the subset-seen flag: the bridge
            // equalities `(map.dom m) == tracked_dom` were asserted inside the
            // popped scope, so re-encoding must re-establish them. Reusing a
            // popped projection would leave it unbridged. Fail-closed: clearing
            // only forfeits memoization, never reuses a stale term.
            enc.state.map_dom_bridges.clear();
            enc.state.map_subset_seen = false;
            enc.set_ematching_round_limit(budget);
            enc
        } else {
            // Fresh setup — either first iteration or previous encoder was lost.
            let enc = AYEncoder::setup_from_prepared_with_extra_variables_and_prune_plan(
                slices,
                use_int_for_measures,
                post_loop_modified_vars,
                extra_variables,
                Some(assertion),
                cached_prune_plan,
            );
            let mut enc = match enc {
                Ok(enc) => enc,
                Err(err) => {
                    tracing::debug!(
                        assertion = %assertion.name,
                        ematching_rounds = budget,
                        error = %format!("{err:?}"),
                        "E-matching escalation encoder setup failed"
                    );
                    return Ok(None);
                }
            };
            enc.set_ematching_round_limit(budget);
            enc
        };

        match verify_assertion_with_timeout_reuse(encoder, assertion, ctx.rlimit_ms)? {
            ReuseAttempt::Completed { encoder, outcome } => match &outcome {
                AssertionOutcome::Verified => {
                    tracing::info!(
                        assertion = %assertion.name,
                        ematching_rounds = budget,
                        "E-matching escalation succeeded (#2720)",
                    );
                    return Ok(Some(AssertionOutcome::Verified));
                }
                AssertionOutcome::Counterexample { .. } | AssertionOutcome::Error { .. } => {
                    return Ok(Some(outcome));
                }
                AssertionOutcome::Unknown { detail, .. } => {
                    let still_retriable = detail.as_ref().is_some_and(|d| d.is_budget_retriable());
                    if !still_retriable {
                        tracing::debug!(
                            assertion = %assertion.name,
                            ematching_rounds = budget,
                            "E-matching escalation: Unknown with non-retriable reason, stopping"
                        );
                        return Ok(None);
                    }
                    // Still budget-retriable — recycle encoder for next level.
                    tracing::debug!(
                        assertion = %assertion.name,
                        ematching_rounds = budget,
                        "E-matching escalation: recycling encoder for next level (#2742)"
                    );
                    recycled_encoder = Some(encoder);
                }
            },
            ReuseAttempt::NonReusable { outcome } => {
                // Encoder's solver scope failed — cannot reuse. Examine outcome.
                match &outcome {
                    AssertionOutcome::Verified => {
                        tracing::info!(
                            assertion = %assertion.name,
                            ematching_rounds = budget,
                            "E-matching escalation succeeded (#2720) (non-reusable)",
                        );
                        return Ok(Some(AssertionOutcome::Verified));
                    }
                    AssertionOutcome::Counterexample { .. } | AssertionOutcome::Error { .. } => {
                        return Ok(Some(outcome));
                    }
                    AssertionOutcome::Unknown { detail, .. } => {
                        let still_retriable =
                            detail.as_ref().is_some_and(|d| d.is_budget_retriable());
                        if !still_retriable {
                            return Ok(None);
                        }
                        // Encoder gone — next iteration creates a fresh one.
                        tracing::debug!(
                            assertion = %assertion.name,
                            ematching_rounds = budget,
                            "E-matching escalation: non-reusable, fresh encoder for next level"
                        );
                    }
                }
            }
            ReuseAttempt::TimedOut => {
                // Encoder consumed by timeout — next iteration creates fresh.
                tracing::debug!(
                    assertion = %assertion.name,
                    ematching_rounds = budget,
                    "E-matching escalation: timed out, fresh encoder for next level"
                );
            }
            ReuseAttempt::Panicked { outcome } => {
                // Encoder in inconsistent state. Check if outcome is useful.
                match &outcome {
                    AssertionOutcome::Verified => {
                        return Ok(Some(AssertionOutcome::Verified));
                    }
                    AssertionOutcome::Counterexample { .. } => {
                        return Ok(Some(outcome));
                    }
                    _ => {
                        tracing::debug!(
                            assertion = %assertion.name,
                            ematching_rounds = budget,
                            "E-matching escalation: panicked, fresh encoder for next level"
                        );
                    }
                }
            }
        }
    }

    Ok(None)
}

#[cfg(test)]
#[path = "assertion_tests.rs"]
mod tests;
