//! Typed verification path — operates directly on PreparedVerificationContext.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Obligations are validated and pre-classified by the validation boundary
//! (`prepared_context::validation`) before reaching the executor. The typed
//! verification path operates on a `ValidatedPreparedContext` whose plan
//! partitions obligations into execution lanes once.
//!
//! All verification paths (assertions, invariant inductive step, overflow
//! checks) operate directly on typed data. No legacy bridges remain.
//!
//! Part of #2219, #1830.

use std::collections::HashSet;
use std::time::Instant;

use super::assertion::verify_single_assertion_typed_with_extra_variables;
use super::outcome::AssertionOutcome;
use super::typed_assertions::verify_regular_assertions;
use super::unknown_category::UnknownCategory;
use super::vacuous::{check_vacuous_truth, demoted_context_result};
use super::VerificationSlices;
use crate::encoder::types::VerifyResult;
use crate::encoder::{diagnostics::EncodingDiagnostics, AYEncoder};
use crate::error::TrustVcResult;
use crate::ir::TrustVcExpr;
use crate::ir_lowering::{lower_syn_expr, TypeEnv};
use crate::prepared_context::validation::{
    validate_prepared_context, ValidatedPreparedContext, ValidationError, VerificationPlan,
};
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
use crate::vc::{is_closure_scoped_obligation_name, ObligationKind, SolverMode};
use crate::verification_report::{self, VerificationPhase};

/// Converts a `ValidationError` into the public `VerifyResult`.
///
/// Opaque variable errors produce `Unknown` (verification skipped) to match the
/// existing behavior of the typed path. All other validation failures produce
/// `Error`. Part of #1830 Slice 3.
fn validation_error_to_result(err: ValidationError) -> VerifyResult {
    match err {
        ValidationError::OpaqueVariable { variables } => {
            let formatted: Vec<_> = variables
                .iter()
                .map(|(name, ty)| format!("'{name}' (type: {ty})"))
                .collect();
            VerifyResult::unknown(
                format!(
                    "Context contains variables with unrecognized types that cannot be \
                     soundly encoded: {}. \
                     Verification skipped to prevent spurious results.",
                    formatted.join(", ")
                ),
                Some(UnknownCategory::OpaqueTypes),
            )
        }
        other => VerifyResult::Error {
            message: other.to_string(),
        },
    }
}

fn finish_reported_typed_step(
    step_index: Option<usize>,
    start: Instant,
    result: TrustVcResult<AssertionOutcome>,
) -> Option<VerifyResult> {
    verification_report::end_step_with_assertion_result(step_index, &result, start.elapsed());
    finish_typed_step(result)
}

/// Concrete-compute recovery for a scoped / `assert_by` obligation whose solver
/// outcome is `Unknown(Incompleteness)`.
///
/// Mirrors the regular-assertion recovery in
/// `typed_assertions::finish_regular_assertion_step`: when the SMT backend
/// reports a *ground, decidable* obligation as quantifier-incomplete, re-check
/// it by concrete evaluation and upgrade to `Verified` ONLY when it evaluates
/// to a definitive `true`.
///
/// The motivating case is an `assert_seqs_equal!` (Seq extensional-equality)
/// goal over concrete `Seq` literals inside a `calc!` proof block. Top-level
/// `assert!`s already receive this recovery via `finish_regular_assertion_step`
/// (so the same goal verifies as a straight-line assert); calc-step scoped
/// assertions and `assert_by` conclusions went through `finish_typed_step`,
/// which lacked it, so the identical ground goal degraded to a spurious
/// `Unknown ((incomplete quantifier-unhandled))`. This restores parity between
/// the two paths.
///
/// SOUNDNESS: identical argument to the regular-assertion recovery. It only
/// ever turns `Unknown -> Verified`, and only when `try_compute_with_bindings`
/// — the same evaluator the regular path trusts — computes the obligation to
/// `true` under its in-scope bindings (assumptions, broadcasts, already-verified
/// assert_by facts, and scoped assumptions). A genuinely-false obligation
/// computes to `false` (or stays unevaluable), so the recovery does nothing and
/// the fail-closed `Unknown` is preserved: it can close a real incompleteness
/// but can never manufacture a spurious `Verified` (nor a `Counterexample`).
fn recover_assert_by_incompleteness_via_compute(
    result: TrustVcResult<AssertionOutcome>,
    slices: &VerificationSlices<'_>,
    assertion: &PreparedObligation,
) -> TrustVcResult<AssertionOutcome> {
    let Ok(outcome) = result else {
        return result;
    };
    let is_incompleteness = match &outcome {
        AssertionOutcome::Unknown {
            reason, category, ..
        } => {
            category.unwrap_or_else(|| UnknownCategory::classify(reason))
                == UnknownCategory::Incompleteness
        }
        _ => false,
    };
    if is_incompleteness
        && super::compute::try_compute_with_bindings(
            &assertion.expr,
            slices.assumptions,
            slices.broadcast_assumptions,
            slices.verified_assert_by,
            slices.scoped_assumptions,
            &slices.ctx.revealed_fns,
            &slices.ctx.hidden_fns,
        ) == Some(true)
    {
        return Ok(AssertionOutcome::Verified);
    }
    Ok(outcome)
}
/// Suffix of the fresh ENTRY symbol a rebound variable's earlier facts are
/// renamed to in a loop invariant's base case (see the entry-rename block).
const LOOP_ENTRY_SUFFIX: &str = "__loop_entry";

/// The variable an entry-scope binding `x == value` rebinds, if the obligation
/// has that shape (over floats, the identity form of
/// [`crate::float_identity::identity_equation`]).
fn entry_binding_target(obligation: &PreparedObligation) -> Option<&str> {
    match crate::float_identity::identity_equation_sides(&obligation.expr)? {
        (crate::ir::TrustVcExpr::Var { name, .. }, _) => Some(name.as_str()),
        _ => None,
    }
}

/// The loop invariants of `goal`'s OWN loop, `goal` itself excluded (2026-09-11).
/// A loop-lane obligation with no registered group (not produced by the
/// file-path extractor) gets no peer hypotheses — sound, possibly incomplete.
fn same_loop_invariants<'a>(
    groups: &std::collections::HashMap<String, usize>,
    invariants: &[&'a PreparedObligation],
    goal: &PreparedObligation,
) -> Vec<&'a PreparedObligation> {
    let Some(group) = groups.get(&goal.name) else {
        return Vec::new();
    };
    invariants
        .iter()
        .copied()
        .filter(|inv| inv.name != goal.name && groups.get(&inv.name) == Some(group))
        .collect()
}

/// The extractor's "code after an infinite loop is unreachable" fact:
/// `post_loop_assumption_pp{N}_unreachable` (see body_extract.rs
/// `add_unreachable_after_infinite_loop`).
fn unreachable_after_infinite_loop_marker(name: &str) -> bool {
    name.starts_with("post_loop_assumption_pp") && name.ends_with("_unreachable")
}

fn scoped_proof_assumption(obligation: &PreparedObligation) -> bool {
    matches!(
        obligation.kind,
        ObligationKind::Assume | ObligationKind::PostLoopAssume
    )
}

fn scoped_proof_assertion(obligation: &PreparedObligation) -> bool {
    matches!(
        obligation.kind,
        ObligationKind::Assert | ObligationKind::Requires
    )
}

/// True iff `obligation` is a straight-line body `assert!` whose VERIFIED truth
/// may be soundly forwarded as an assumption to later obligations on the same
/// path (notably postconditions). Part of #2778.
///
/// Restricted to `ObligationKind::Assert` obligations that are NOT the
/// postcondition. The postcondition (the `ensures` clause) is materialized as an
/// `Assert` named `"postcondition"` (attr_extract) — it is excluded so that no
/// postcondition is ever forwarded as an assumption (strictly more conservative
/// than Verus, which does allow earlier-proven ensures). `ObligationKind::Ensures`
/// obligations are likewise excluded.
///
/// `Compute`-mode asserts are excluded: they are discharged by concrete
/// evaluation rather than SMT encoding, so they are not encoded into the
/// assumption set and forwarding them would be a no-op at best.
///
/// SOUNDNESS: trust-vc lowers a branch-local body assert to a flat `Assert`
/// obligation with NO branch guard, so a VERIFIED body assert necessarily holds
/// UNCONDITIONALLY under the requires (a branch-local-only fact fails closed).
/// Forwarding such an unconditionally-proven fact as an assumption is therefore
/// sound.
pub(super) fn forwardable_body_assert(obligation: &PreparedObligation) -> bool {
    obligation.kind == ObligationKind::Assert
        && obligation.name != "postcondition"
        && !matches!(obligation.solver_mode, Some(SolverMode::Compute))
}

/// True iff `obligation` is the function-level postcondition (an `ensures`
/// clause from a contract attribute).
///
/// The function `ensures` clause is always materialized as an
/// `ObligationKind::Assert` named exactly `"postcondition"` by `attr_extract`
/// (and `trait_contracts`). This is the obligation Verus verifies LAST and the
/// one whose truth may depend on a witness established by a later straight-line
/// body assert, so it is the one that benefits from forwarding.
///
/// `ObligationKind::Ensures` obligations are intentionally NOT matched here: they
/// are produced by internal mechanisms (e.g. `__option_*_closure_ensures`) that
/// may be interleaved among body asserts, and they are not function
/// postconditions. Keeping them in their original position avoids any reordering
/// of the assertion stream. Part of #2778.
fn postcondition_obligation(obligation: &PreparedObligation) -> bool {
    obligation.kind == ObligationKind::Assert && obligation.name == "postcondition"
}

fn calc_step_exports_after_verification(assert_by: &PreparedObligation) -> bool {
    let Some(meta) = assert_by.step_meta.as_ref() else {
        return !looks_like_calc_step_name(&assert_by.name);
    };
    let label = meta.label();
    if let Some((_, total)) = label.rsplit_once(" of ") {
        if label.starts_with("calc step ") {
            return total
                .trim()
                .parse::<usize>()
                .map_or(true, |total| total <= 1);
        }
    }
    !looks_like_calc_step_name(&assert_by.name)
}

fn looks_like_calc_step_name(name: &str) -> bool {
    !name.contains("_conclusion_step_")
        && (name.starts_with("calc_") || name.starts_with("calc_line_"))
        && name.contains("_step_")
}

fn verify_compute_mode_obligation(
    assertion: &PreparedObligation,
    slices: &VerificationSlices<'_>,
) -> Option<AssertionOutcome> {
    if assertion.solver_mode != Some(SolverMode::Compute) {
        return None;
    }
    match super::compute::try_compute_with_bindings(
        &assertion.expr,
        slices.assumptions,
        slices.broadcast_assumptions,
        slices.verified_assert_by,
        slices.scoped_assumptions,
        &slices.ctx.revealed_fns,
        &slices.ctx.hidden_fns,
    ) {
        Some(true) => Some(AssertionOutcome::Verified),
        Some(false) => Some(AssertionOutcome::Counterexample {
            obligation_name: assertion.name.clone(),
            location: assertion.location.clone(),
            model: Some("by(compute): expression evaluates to false".to_string()),
            bindings: Vec::new(),
        }),
        None => Some(AssertionOutcome::unknown(
            format!(
                "Compute mode: '{}' contains symbolic variables or expressions that cannot be fully evaluated. by(compute) requires all values to be concrete.",
                assertion.name,
            ),
            None,
        )),
    }
}

impl AYEncoder {
    /// Typed verification entrypoint — validates, then executes.
    ///
    /// Runs the validation boundary on `PreparedVerificationContext`, producing
    /// a pre-classified execution plan, then delegates to `verify_validated()`
    /// which trusts the plan without re-partitioning obligation kinds.
    /// Part of #2219, #1830 Slice 3.
    pub(in crate::encoder) fn verify_typed(ctx: &PreparedVerificationContext) -> VerifyResult {
        match validate_prepared_context(ctx) {
            Ok(validated) => Self::verify_validated(&validated),
            Err(err) => validation_error_to_result(err),
        }
    }

    /// Executes a pre-validated verification plan.
    ///
    /// Receives a `ValidatedPreparedContext` where obligations have already been
    /// classified into execution lanes by the validation boundary. Does not
    /// re-partition obligation kinds. Part of #1830 Slice 3.
    fn verify_validated(validated: &ValidatedPreparedContext<'_>) -> VerifyResult {
        let ctx = validated.source;
        let plan = &validated.plan;
        let mut vacuous_precheck_diagnostics = EncodingDiagnostics::default();

        // Loop invariants
        let mut verified_invariant_obligations: Vec<&PreparedObligation> = Vec::new();
        for invariant in &plan.loop_invariants {
            // The invariants of THIS loop (all of them, itself excluded — the
            // step adds the goal at the pre-state itself): the only
            // pre-state hypotheses of the base case and the inductive step.
            let loop_peers =
                same_loop_invariants(&ctx.loop_invariant_groups, &plan.loop_invariants, invariant);
            // Base case: typed path (current-state assumptions, no post-loop framing)
            let step = verification_report::begin_obligation_step(
                VerificationPhase::LoopInvariant,
                invariant,
            );
            let start = Instant::now();
            // ENTRY (base case) only: a loop-modified let-local's pre-loop value
            // (`i == 0`) is fed through the SCOPED slot so it pins the entry check
            // exactly like a param's `requires`, WITHOUT entering the inductive
            // step or post-loop lanes (which havoc the modified var) and WITHOUT
            // tripping the current-state vacuity precheck against the negated-guard
            // exit fact. Empty for param-only loops. Mirrors the assert_by scope.
            let entry_scope = ctx
                .loop_entry_scopes
                .get(&invariant.name)
                .map(|v| v.iter().collect::<Vec<_>>())
                .unwrap_or_default();
            let entry_scoped_assumptions = entry_scope
                .iter()
                .copied()
                .filter(|obligation| scoped_proof_assumption(obligation))
                .collect::<Vec<_>>();
            // SOUNDNESS-CRITICAL (post-loop exit fact leaking into the ENTRY
            // check — a confirmed false-verify for let-local loop counters): the
            // base (establishment) check runs at LOOP ENTRY, before the loop body
            // executes. The auto-generated negated-guard exit fact
            // (`post_loop_assumption_*`, e.g. `!(i < 3)`) is a POST-loop fact that
            // does NOT hold at entry. Left in scope alongside the loop's entry
            // binding (`i == 0`) it makes the entry context contradictory
            // (`i == 0 ∧ i >= 3`), so ANY invariant — including a false one like
            // `i == 100` — VACUOUSLY verifies at the base case. Exclude post-loop
            // facts from the base check. Fail-closed and cannot over-reject a
            // genuine invariant: the excluded fact is not yet true at entry, so
            // dropping it only makes the establishment obligation stricter.
            // NESTED ENTRY (2026-09-10): the base case of a loop nested in
            // another loop's body runs at an ARBITRARY head of the enclosing
            // loop. A plan assumption about a var this loop modifies (a
            // `requires` on a `mut` param, say) speaks of the FUNCTION entry,
            // not this entry — kept, it let an inner invariant that holds only
            // on the first enclosing iteration verify (`requires(total == 0)`
            // + `invariant!(total <= 5)` with `total` growing outside). The
            // entry scope binds the var to its site value over the enclosing
            // head instead, and the predicate carries the enclosing guard ∧
            // invariants, so dropping those assumptions loses nothing true.
            let nested_modified: Option<HashSet<String>> = ctx
                .loop_nested_entry_invariants
                .contains(&invariant.name)
                .then(|| {
                    ctx.loop_modified_vars
                        .get(&invariant.name)
                        .map(|vars| vars.iter().cloned().collect())
                        .unwrap_or_default()
                });
            // ENTRY RENAME (2026-09-11, `tests/preloop_assignment_declared_var_soundness.rs`):
            // a var the entry scope REBINDS (`x == <pre-loop value>`, a declared
            // var assigned before the loop, or an inner-modified var bound to its
            // site value) has ONE symbol for two states — the bare name is the
            // loop-head value in the binding and the goal, but every earlier plan
            // fact (`requires(x == 5)`, a call's ensures) speaks of the FUNCTION
            // entry. Kept as written those facts contradict the binding
            // (`x == 5 ∧ x == 0`; `x == x + 1`) and the base case verified
            // VACUOUSLY (two measured false-verifies). So, in the base case only,
            // every rebound var (and every var of a nested loop's modified set —
            // formerly DROPPED) is renamed to a fresh entry symbol
            // `x__loop_entry` in those facts AND in the bindings' right-hand
            // sides: the facts now describe the entry value, the binding
            // connects the head value to it (`x == x__loop_entry + 1`), and
            // nothing true is lost.
            let mut rename_targets: HashSet<String> = nested_modified.clone().unwrap_or_default();
            for obligation in &entry_scoped_assumptions {
                if let Some(name) = entry_binding_target(obligation) {
                    rename_targets.insert(name.to_string());
                }
            }
            let rename_refs: HashSet<&str> = rename_targets.iter().map(String::as_str).collect();
            let renamed_base: Vec<PreparedObligation> = plan
                .assumptions
                .iter()
                .copied()
                .filter(|obligation| !obligation.name.starts_with("post_loop_assumption"))
                .map(|obligation| {
                    if rename_refs.is_empty() {
                        return obligation.clone();
                    }
                    let referenced =
                        super::invariants::frame_condition::collect_referenced_var_names(
                            &obligation.expr,
                        );
                    if !referenced.iter().any(|name| rename_targets.contains(name)) {
                        return obligation.clone();
                    }
                    let mut renamed = obligation.clone();
                    renamed.expr = super::rewrite::rename_vars_with_suffix_typed(
                        &obligation.expr,
                        &rename_refs,
                        LOOP_ENTRY_SUFFIX,
                    );
                    renamed
                })
                .collect();
            let base_assumptions: Vec<&PreparedObligation> = renamed_base.iter().collect();
            let renamed_entry_scope: Vec<PreparedObligation> = entry_scoped_assumptions
                .iter()
                .map(|obligation| {
                    if rename_refs.is_empty() {
                        return (*obligation).clone();
                    }
                    let mut renamed = (*obligation).clone();
                    let binding = entry_binding_target(obligation).and_then(|_| {
                        crate::float_identity::identity_equation_sides(&obligation.expr)
                    });
                    renamed.expr = match binding {
                        // `x == value`: the head value `x` stays, the value is
                        // over the entry symbols.
                        Some((left, right)) => crate::float_identity::identity_equation(
                            left.clone(),
                            super::rewrite::rename_vars_with_suffix_typed(
                                right,
                                &rename_refs,
                                LOOP_ENTRY_SUFFIX,
                            ),
                        ),
                        None => super::rewrite::rename_vars_with_suffix_typed(
                            &obligation.expr,
                            &rename_refs,
                            LOOP_ENTRY_SUFFIX,
                        ),
                    };
                    renamed
                })
                .collect();
            let entry_scope_refs: Vec<&PreparedObligation> = renamed_entry_scope.iter().collect();
            let entry_variables: Vec<crate::vc::VariableDecl> = ctx
                .variables
                .iter()
                .filter(|decl| rename_targets.contains(&decl.name))
                .map(|decl| {
                    crate::vc::VariableDecl::new(
                        format!("{}{}", decl.name, LOOP_ENTRY_SUFFIX),
                        decl.ty.clone(),
                    )
                })
                .collect();
            let slices = VerificationSlices::new(
                ctx,
                &base_assumptions,
                &plan.broadcast_assumptions,
                &loop_peers,
                &[],
                &entry_scope_refs,
            );
            if let Some(result) = finish_reported_typed_step(
                step,
                start,
                Self::verify_typed_step(&slices, &entry_variables, invariant, None),
            ) {
                return result;
            }
            // Inductive step: typed path (no legacy bridge). The pre-state
            // hypotheses are the invariants of the SAME loop (2026-09-11) —
            // before, every previously verified invariant of the FUNCTION was
            // assumed, so an earlier loop's `x == 10` reached a later loop's
            // head and "preserved" a false `x <= 11` there (measured
            // false-verify, `tests/loop_invariant_scope_soundness.rs`).
            let step = verification_report::begin_obligation_step(
                VerificationPhase::LoopInvariantInductiveStep,
                invariant,
            );
            let start = Instant::now();
            let inductive_result =
                Self::verify_invariant_inductive_step_typed(ctx, invariant, &loop_peers);
            verification_report::end_step_with_assertion_result(
                step,
                &inductive_result,
                start.elapsed(),
            );
            match inductive_result {
                Ok(AssertionOutcome::Verified) => {}
                Ok(AssertionOutcome::Counterexample {
                    model, bindings, ..
                }) => {
                    let obligation_name = format!("{} (inductive step)", invariant.display_name());
                    return VerifyResult::Counterexample {
                        obligation_name,
                        location: invariant.location.clone(),
                        model,
                        bindings,
                    };
                }
                Ok(AssertionOutcome::Unknown {
                    reason, category, ..
                }) => {
                    return VerifyResult::unknown(reason, category);
                }
                Ok(AssertionOutcome::Error { message }) => {
                    return VerifyResult::Error { message };
                }
                Err(err) => return VerifyResult::from(err),
            }
            verified_invariant_obligations.push(invariant);
        }

        // Loop termination measures (`loop_decreases!`): a well-founded-measure
        // invariant, proven by TWO INDEPENDENT obligations per measure —
        //
        //   WF1 (non-negativity FLOOR): `Inv(s) && G(s) |= M(s) >= 0`, a DIRECT
        //   single-state entailment (see `verify_measure_nonneg_floor`). It is
        //   deliberately NOT an inductive step: an inductive step assumes
        //   `M(pre) >= 0` as its induction hypothesis, and under a negative
        //   invariant (e.g. `i < 0`) that hypothesis CONTRADICTS the invariant,
        //   vacuously discharging the floor — the exact hole this lane was
        //   quarantined for (a strictly-decreasing but unbounded-below `int`
        //   measure was accepted as terminating). The floor is refuted whenever
        //   `Inv && G` admit a negative measure, in the measure's own int sort.
        //
        //   WF2 (strict DESCENT): `Inv(s) && G(s) && s' = f(s) |= M(s') < M(s)`,
        //   a frame-condition INDUCTIVE step (`verify_invariant_inductive_step_typed`),
        //   with the entry var BOUND (not free) from the exact single-iteration
        //   transition `entry_var == M(pre)`. There is no base case (a decrease is
        //   trivially false at loop entry). Exec measures also run the inductive
        //   step's overflow pass as redundant belt-and-suspenders for expression
        //   underflow (e.g. `5u64 - i`).
        //
        // SOUNDNESS (continue/break non-termination landmine): a measure whose
        // loop body admitted no exact transition (non-flat body, `continue`/
        // `break`, bare `loop{}`/`for`) carries NO loop metadata, so
        // `classify_obligations` never routes it here — it stays in the flat
        // `assertions` lane with a free entry variable / havoc'd loop var and
        // fails closed as a Counterexample. Part of the file-path `loop_decreases!`
        // wiring.
        for measure in &plan.loop_measures {
            let measure_peers =
                same_loop_invariants(&ctx.loop_invariant_groups, &plan.loop_invariants, measure);
            match measure.kind {
                ObligationKind::MeasureNonNegative => {
                    // WF1: non-negativity floor, direct single-state entailment.
                    if let Some(result) =
                        Self::verify_measure_nonneg_floor(ctx, plan, measure, &measure_peers)
                    {
                        return result;
                    }
                }
                ObligationKind::MeasureDecreases => {
                    // WF2: strict descent, frame-condition inductive step.
                    //
                    // Exec (Uint/BV) measures WRAP without overflow checking,
                    // which would let a wrapped subtraction feign a decrease, so
                    // fail closed here. The WF1 floor above is proven in int mode
                    // and does NOT depend on this gate (`loop_decreases!` is an
                    // exec-loop construct, so overflow checking is normally on;
                    // this guards spec/wrapping modes).
                    if !ctx.check_overflow() {
                        return VerifyResult::unknown(
                            "loop_decreases! strict-descent step cannot be soundly discharged \
                             without overflow checking (exec measures wrap)",
                            None,
                        );
                    }
                    let step = verification_report::begin_obligation_step(
                        VerificationPhase::LoopDecreases,
                        measure,
                    );
                    let start = Instant::now();
                    let inductive_result =
                        Self::verify_invariant_inductive_step_typed(ctx, measure, &measure_peers);
                    verification_report::end_step_with_assertion_result(
                        step,
                        &inductive_result,
                        start.elapsed(),
                    );
                    match inductive_result {
                        Ok(AssertionOutcome::Verified) => {}
                        Ok(AssertionOutcome::Counterexample {
                            model, bindings, ..
                        }) => {
                            let obligation_name = format!("{} (decreases)", measure.display_name());
                            return VerifyResult::Counterexample {
                                obligation_name,
                                location: measure.location.clone(),
                                model,
                                bindings,
                            };
                        }
                        Ok(AssertionOutcome::Unknown {
                            reason, category, ..
                        }) => {
                            return VerifyResult::unknown(reason, category);
                        }
                        Ok(AssertionOutcome::Error { message }) => {
                            return VerifyResult::Error { message };
                        }
                        Err(err) => return VerifyResult::from(err),
                    }
                }
                _ => {}
            }
        }

        // Partition verified invariants: LoopInvariant facts are available
        // unconditionally after the loop; InvariantExceptBreak facts are only
        // available on the normal-exit path (guard becomes false). For post-loop
        // assertions we use only always_available. Part of #2417.
        //
        // SOUNDNESS-CRITICAL (H7 review round 2): a `closure_scoped__` invariant
        // belongs to a loop inside a CLOSURE LITERAL's body that modifies a
        // symbol the enclosing function also names. Its base case was discharged
        // from closure-local state (`|| { x = 0; while x < 10 { invariant!(x <=
        // 10); .. } }`), and the closure need never run, so the verified
        // predicate must NOT become a function-wide post-loop fact — it reached
        // the postcondition lane, which reads a by-value `mut` parameter's bare
        // symbol and cannot be protected by the after-the-closure capture havoc
        // (measured `Verified` on `3fab140f`). It is still CHECKED in full and
        // still contributes its modified variables to `post_loop_modified_vars`
        // below, so this only ever removes a hypothesis.
        let always_available_invariants: Vec<&PreparedObligation> = verified_invariant_obligations
            .iter()
            .filter(|o| {
                o.kind == ObligationKind::LoopInvariant
                    && !is_closure_scoped_obligation_name(&o.name)
            })
            .copied()
            .collect();

        // Compute the union of modified variables from all verified loop
        // invariants. Post-loop proof steps use this to forget entry
        // assumptions about modified variables. Part of #2448.
        let post_loop_modified_vars: Option<HashSet<String>> =
            if !verified_invariant_obligations.is_empty() {
                let vars: HashSet<String> = verified_invariant_obligations
                    .iter()
                    .filter_map(|inv| ctx.loop_modified_vars.get(&inv.name))
                    .flat_map(|vars| vars.iter().cloned())
                    .collect();
                if vars.is_empty() {
                    None // No modified vars → keep current-state fast path.
                } else {
                    Some(vars)
                }
            } else {
                None
            };

        // Loop ensures: assume all verified invariants + ¬guard → ensures.
        // Verifies that the loop postcondition holds on normal exit. Part of #2417.
        // If multiple LoopGuard obligations are present, we fall back to the
        // invariant-only check rather than guessing which guard belongs to
        // this ensures clause. That keeps the check conservative.
        let normal_exit_guard = match plan.loop_guards.as_slice() {
            [guard] => Some(PreparedObligation {
                name: format!("{}_normal_exit", guard.name),
                kind: ObligationKind::Assume,
                location: guard.location.clone(),
                condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
                bound_vars: None,
                trigger_patterns: None,
                prepared_triggers: None,
                solver_mode: None,
                is_opaque: false,
                is_inline: false,
                broadcast_group: None,
                condition: format!("!({})", guard.condition),
                expr: crate::ir::TrustVcExpr::Not(Box::new(guard.expr.clone())),
                invariant_namespace: None,
                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
            }),
            _ => None,
        };
        let mut normal_exit_assumptions: Vec<&PreparedObligation> = Vec::new();
        if let Some(ref guard) = normal_exit_guard {
            normal_exit_assumptions.push(guard);
        }
        // Verified loop_ensures are post-loop facts: they are not available to
        // prove other loop_ensures, but following proof steps may use them.
        let mut verified_loop_ensures: Vec<&PreparedObligation> = Vec::new();
        for ensures_ob in &plan.loop_ensures {
            let ensures_peers = same_loop_invariants(
                &ctx.loop_invariant_groups,
                &plan.loop_invariants,
                ensures_ob,
            );
            // EXIT-SITE form (audit rows 430/431): a `loop_ensures` registered in
            // `loop_modified_vars` is a break-site check emitted by the file-path
            // extractor — "from any loop head satisfying the invariants and the
            // loop guard, if the body runs to this break site and its condition
            // holds, the predicate holds there". It is verified as a
            // frame-condition inductive step under its OWN metadata (guard
            // `head ∧ cond_site`, site transition) and has NO base case: an
            // `ensures` need not hold at loop entry. The verified predicate is a
            // post-loop fact exactly like the normal-exit form below.
            if ctx.loop_modified_vars.contains_key(&ensures_ob.name) {
                let step = verification_report::begin_obligation_step(
                    VerificationPhase::LoopEnsures,
                    ensures_ob,
                );
                let start = Instant::now();
                let inductive_result =
                    Self::verify_exit_check_step_typed(ctx, ensures_ob, &ensures_peers);
                verification_report::end_step_with_assertion_result(
                    step,
                    &inductive_result,
                    start.elapsed(),
                );
                match inductive_result {
                    Ok(AssertionOutcome::Verified) => {}
                    Ok(AssertionOutcome::Counterexample {
                        model, bindings, ..
                    }) => {
                        let obligation_name =
                            format!("{} (at break exit)", ensures_ob.display_name());
                        return VerifyResult::Counterexample {
                            obligation_name,
                            location: ensures_ob.location.clone(),
                            model,
                            bindings,
                        };
                    }
                    Ok(AssertionOutcome::Unknown {
                        reason, category, ..
                    }) => {
                        return VerifyResult::unknown(reason, category);
                    }
                    Ok(AssertionOutcome::Error { message }) => {
                        return VerifyResult::Error { message };
                    }
                    Err(err) => return VerifyResult::from(err),
                }
                // A CONTINUE-site check proves the predicate on a path back to
                // the head, not at an exit: it is not a post-loop fact (an
                // except-break invariant proven at a `continue` must not
                // survive a later `break`).
                // A `closure_scoped__` exit-site copy belongs to a loop inside
                // a closure literal's body that modifies an outer-nameable
                // symbol: same channel, same suppression (H7 review round 2).
                if !ensures_ob.name.starts_with("loop_continue_check_")
                    && !is_closure_scoped_obligation_name(&ensures_ob.name)
                {
                    verified_loop_ensures.push(ensures_ob);
                }
                continue;
            }
            let step = verification_report::begin_obligation_step(
                VerificationPhase::LoopEnsures,
                ensures_ob,
            );
            let start = Instant::now();
            // NORMAL-EXIT GUARD, FILE PATH (2026-09-11): the extractor stores a
            // loop's guard as a STRING in `ctx.loop_guards` under the ensures'
            // own name (no `LoopGuard` obligation reaches `plan.loop_guards`),
            // and for a loop that also `break`s it withholds the global
            // normal-exit fact — rightly, the post-loop state may come from a
            // break. The normal-exit copy of a `loop_ensures` is nevertheless
            // "invariants ∧ ¬guard ⊢ ensures", so lower `!(guard)` here as a
            // lane-local scoped assumption for THIS obligation only.
            let file_path_normal_exit = if normal_exit_guard.is_none() {
                ctx.loop_guards
                    .get(&ensures_ob.name)
                    .and_then(|condition| {
                        Self::lower_measure_guard(ctx, condition).map(|expr| (condition, expr))
                    })
                    .map(|(condition, expr)| PreparedObligation {
                        name: format!("{}_normal_exit", ensures_ob.name),
                        kind: ObligationKind::Assume,
                        location: ensures_ob.location.clone(),
                        condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
                        bound_vars: None,
                        trigger_patterns: None,
                        prepared_triggers: None,
                        solver_mode: None,
                        is_opaque: false,
                        is_inline: false,
                        broadcast_group: None,
                        condition: format!("!({condition})"),
                        expr: crate::ir::TrustVcExpr::Not(Box::new(expr)),
                        invariant_namespace: None,
                        trigger_inference_mode: None,
                        broadcast_guard: None,
                        raw_broadcast_guard_count: 0,
                        step_meta: None,
                    })
            } else {
                None
            };
            let mut ensures_scope: Vec<&PreparedObligation> = normal_exit_assumptions.clone();
            if let Some(ref guard) = file_path_normal_exit {
                ensures_scope.push(guard);
            }
            let slices = VerificationSlices::new(
                ctx,
                &plan.assumptions,
                &plan.broadcast_assumptions,
                &ensures_peers,
                &[],
                &ensures_scope,
            );
            if let Some(result) = finish_reported_typed_step(
                step,
                start,
                Self::verify_typed_step(&slices, &[], ensures_ob, post_loop_modified_vars.as_ref()),
            ) {
                return result;
            }
            verified_loop_ensures.push(ensures_ob);
        }

        // Assert_by
        // VACUITY PRECHECK — run AFTER the loop lanes (moved 2026-09-10) and
        // BEFORE every assertion lane. The loop lanes prove their goals under
        // their own assumption subsets (the base case excludes post-loop facts,
        // the frame-condition steps exclude `PostLoopAssume` entirely), so a
        // context that is contradictory only through a loop's exit fact — a
        // `while` whose guard can never fail, upstream loop_decreases2 test3 —
        // still surfaces its genuine loop failure (the measure's descent) as a
        // Counterexample, as Verus reports it, instead of a blanket vacuity
        // Unknown. Nothing is reported Verified before this check runs: a
        // contradictory `requires` makes the loop lanes vacuous (never refuted)
        // and the precheck then returns exactly the Unknown it always returned.
        let vacuous_step = verification_report::begin_step(
            VerificationPhase::VacuousPrecheck,
            "vacuous truth precheck",
            None,
        );
        let vacuous_start = Instant::now();
        // Frame the precheck like the post-loop lanes (see `run_vacuous_precheck`):
        // the union of every loop invariant's modified set, `None` when the
        // function has no loop metadata (then the precheck is unchanged).
        let precheck_modified_vars: Option<HashSet<String>> = {
            let vars: HashSet<String> = plan
                .loop_invariants
                .iter()
                .filter_map(|inv| ctx.loop_modified_vars.get(&inv.name))
                .flat_map(|vars| vars.iter().cloned())
                .collect();
            (!vars.is_empty()).then_some(vars)
        };
        // A bare `loop {}` with no exit marks the code after it unreachable
        // with the post-loop fact `false` (`…_unreachable`, body_extract.rs
        // `add_unreachable_after_infinite_loop`). That is a deliberate
        // divergence, not a contradictory precondition, so the precheck skips
        // the marker; every other lane treats it exactly like a normal-exit fact.
        let precheck_assumptions: Vec<&PreparedObligation> = plan
            .assumptions
            .iter()
            .copied()
            .filter(|obligation| !unreachable_after_infinite_loop_marker(&obligation.name))
            .collect();
        let vacuous_result = check_vacuous_truth(
            ctx,
            &precheck_assumptions,
            &plan.broadcast_assumptions,
            precheck_modified_vars.as_ref(),
            &mut vacuous_precheck_diagnostics,
        );
        match vacuous_result.as_ref() {
            Some(result) => verification_report::end_step_with_verify_result(
                vacuous_step,
                result,
                vacuous_start.elapsed(),
            ),
            None => verification_report::end_step_skipped(vacuous_step, vacuous_start.elapsed()),
        }
        if let Some(result) = vacuous_result {
            return result;
        }

        let mut verified_assert_by: Vec<&PreparedObligation> = Vec::new();
        for assert_by in &plan.assert_by {
            // ── SCOPED REVEAL (#34, upstream assert_forall_by.rs) ─────────────
            // A `reveal!(f)` written INSIDE this by-block applies ONLY while
            // verifying this block: its inner assertions AND its conclusion. The
            // proven conclusion still persists as a fact afterwards
            // (`verified_assert_by`, upstream `test_assertby1`), but `f` is
            // opaque again for every later obligation (upstream
            // `test_assertby1_fail2`).
            //
            // Implemented by verifying this scope against a CLONE of the context
            // whose `revealed_fns` is the query set UNIONED with the scope's
            // reveals. Every downstream consumer (opaque body-axiom broadcast
            // gate, inline-hide gate, compute catalog, demand-inline catalog)
            // reads `slices.ctx.revealed_fns`, so the union reaches all of them —
            // and NOTHING outside this loop iteration sees the clone, so
            // `ctx.revealed_fns` is byte-identical to its pre-#34 value for every
            // other obligation. When the scope has no `reveal!` (the overwhelming
            // majority) no clone is made and the code path is unchanged.
            let scope_revealed_fns = ctx.assert_by_scope_revealed_fns.get(&assert_by.name);
            let scoped_reveal_ctx;
            let ctx: &PreparedVerificationContext = match scope_revealed_fns {
                Some(revealed) if !revealed.is_empty() => {
                    let mut cloned = ctx.clone();
                    cloned.revealed_fns.extend(revealed.iter().cloned());
                    scoped_reveal_ctx = cloned;
                    &scoped_reveal_ctx
                }
                _ => ctx,
            };

            let forall_bound_vars = ctx
                .forall_bound_vars
                .get(&assert_by.name)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            let scoped = match ctx
                .assert_by_scopes
                .get(&assert_by.name)
                .map(|v| v.iter().collect::<Vec<_>>())
            {
                Some(scoped) => scoped,
                None => {
                    return VerifyResult::from(crate::error::TrustVcError::Internal {
                        context: "verify typed assert_by obligation",
                        detail: format!(
                            "Missing prepared assert_by scope '{}' for obligation '{}'",
                            assert_by.name, assert_by.name
                        ),
                    });
                }
            };
            let scoped_assumptions = scoped
                .iter()
                .copied()
                .filter(|obligation| scoped_proof_assumption(obligation))
                .collect::<Vec<_>>();
            let mut verified_assert_by_for_scope = verified_assert_by.clone();
            verified_assert_by_for_scope.extend(verified_loop_ensures.iter().copied());

            for scoped_assertion in scoped
                .iter()
                .copied()
                .filter(|obligation| scoped_proof_assertion(obligation))
            {
                let step = verification_report::begin_obligation_step(
                    VerificationPhase::AssertBy,
                    scoped_assertion,
                );
                let start = Instant::now();
                let requires_slices = VerificationSlices::new(
                    ctx,
                    &plan.assumptions,
                    &plan.broadcast_assumptions,
                    &always_available_invariants,
                    &verified_assert_by_for_scope,
                    &scoped_assumptions,
                );
                if let Some(result) = finish_reported_typed_step(
                    step,
                    start,
                    recover_assert_by_incompleteness_via_compute(
                        Self::verify_typed_step(
                            &requires_slices,
                            forall_bound_vars,
                            scoped_assertion,
                            post_loop_modified_vars.as_ref(),
                        ),
                        &requires_slices,
                        scoped_assertion,
                    ),
                ) {
                    return result;
                }
                verified_assert_by_for_scope.push(scoped_assertion);
            }
            let step =
                verification_report::begin_obligation_step(VerificationPhase::AssertBy, assert_by);
            let start = Instant::now();
            let slices = VerificationSlices::new(
                ctx,
                &plan.assumptions,
                &plan.broadcast_assumptions,
                &always_available_invariants,
                &verified_assert_by_for_scope,
                &scoped_assumptions,
            );
            let assert_by_result = verify_compute_mode_obligation(assert_by, &slices)
                .map(Ok)
                .unwrap_or_else(|| {
                    recover_assert_by_incompleteness_via_compute(
                        Self::verify_typed_step(
                            &slices,
                            forall_bound_vars,
                            assert_by,
                            post_loop_modified_vars.as_ref(),
                        ),
                        &slices,
                        assert_by,
                    )
                });
            if let Some(result) = finish_reported_typed_step(step, start, assert_by_result) {
                return result;
            }
            if calc_step_exports_after_verification(assert_by) {
                verified_assert_by.push(assert_by);
            }
        }

        let mut verified_post_loop_facts = verified_assert_by.clone();
        verified_post_loop_facts.extend(verified_loop_ensures.iter().copied());

        // Regular assertions (shared-BV fast path + compute mode dispatch).
        // Extracted to typed_assertions module. Part of #2621.
        //
        // ── Assumption forwarding (#2778) ──────────────────────────────────
        // Verus verifies postconditions LAST and carries forward proven
        // straight-line body facts. trust-vc's obligation order, however, pushes
        // the postcondition (the `ensures` clause, materialized as an
        // `Assert` named "postcondition" / `Ensures`) BEFORE the body asserts
        // (attr_extract runs before body_extract). Without forwarding, a
        // postcondition whose truth depends on a witness established by a later
        // straight-line body assert (e.g. `archimedean_nat`: body
        // `assert(x < nat_to_real(a+1))` establishes the exists-witness for
        // `ensures exists |n| ... >= x`) is checked against only the
        // requires-derived assumptions and spuriously fails as a Counterexample.
        //
        // Sound + additive fix WITHOUT changing obligation capture order/counts:
        //  1. A capture-SUPPRESSED pre-pass verifies the forwardable
        //     straight-line body asserts; the ones that verify become forwarded
        //     assumptions. (Suppressed ⇒ adds no obligation steps/fingerprints,
        //     so the manifest's pinned obligation accounting is unchanged. A
        //     body assert that fails the pre-pass is simply not forwarded; it
        //     will be reported by the real pass below.)
        //  2. The real verification runs in the original plan order: the
        //     postcondition group first (it is already first in plan order),
        //     then the remaining obligations. Postconditions are verified WITH
        //     the forwarded asserts available; everything else keeps its exact
        //     prior assumption set. This preserves the pre-existing
        //     capture/abort behavior (a failing body assert still short-circuits
        //     exactly as before, after the already-captured postcondition).
        //
        // SOUNDNESS: trust-vc's body-assert VC model is path-insensitive — a body
        // assert inside an `if` branch is lowered to a flat `Assert` obligation
        // with NO branch guard, so it can only verify if it holds UNCONDITIONALLY
        // under the requires (a branch-local-only fact fails closed as a
        // Counterexample). Therefore a VERIFIED body assert is an unconditional
        // fact at the requires level, and forwarding it as an unconditional
        // assumption to the postcondition is sound modus-ponens forwarding of an
        // already-proven fact. Only asserts that ACTUALLY verify (pre-pass) are
        // forwarded; postconditions/ensures are themselves never forwarded
        // (strictly more conservative than Verus). Part of #2778.
        let (postconditions, non_postcondition_assertions): (
            Vec<&PreparedObligation>,
            Vec<&PreparedObligation>,
        ) = plan
            .assertions
            .iter()
            .copied()
            .partition(|obligation| postcondition_obligation(obligation));

        // Forwarding only matters when there is both a postcondition AND at least
        // one straight-line body assert. Skip the pre-pass otherwise to avoid any
        // extra solver work.
        let forwardable_candidates: Vec<&PreparedObligation> = if postconditions.is_empty() {
            Vec::new()
        } else {
            non_postcondition_assertions
                .iter()
                .copied()
                .filter(|obligation| forwardable_body_assert(obligation))
                .collect()
        };

        let mut forwarded_body_asserts: Vec<&PreparedObligation> = Vec::new();
        if !forwardable_candidates.is_empty() {
            // Capture-suppressed pre-pass: a body assert is forwarded only if it
            // independently verifies under the requires-derived assumptions.
            for candidate in &forwardable_candidates {
                let candidate_slices = VerificationSlices::new(
                    ctx,
                    &plan.assumptions,
                    &plan.broadcast_assumptions,
                    &always_available_invariants,
                    &verified_post_loop_facts,
                    &[],
                );
                // A closed-ground datatype (dis)equality goal that the concrete
                // evaluator reduces to `false` is REFUTED: it cannot verify, so
                // it must not be forwarded. Deciding that here rather than by
                // solving is fail-closed twice over — it only ever REMOVES a
                // candidate assumption (the postcondition is then proved under a
                // strictly weaker context, so nothing can newly verify), and it
                // closes the hazard that ay's unsound depth-1 datatype-`eq`
                // UNSAT hands this pre-pass a `Verified` for a FALSE fact which
                // is then forwarded as a true hypothesis — the pre-pass runs
                // through `verify_typed_step`, where neither the datatype-`!=`
                // re-validation nor the reflexive demote applies.
                if super::typed_assertions::closed_ground_datatype_goal_computes_false(
                    &candidate_slices,
                    candidate,
                ) {
                    continue;
                }
                let verified = verification_report::with_capture_suppressed(|| {
                    matches!(
                        Self::verify_typed_step(
                            &candidate_slices,
                            &[],
                            candidate,
                            post_loop_modified_vars.as_ref(),
                        ),
                        Ok(AssertionOutcome::Verified)
                    )
                });
                if verified {
                    forwarded_body_asserts.push(candidate);
                }
            }
        }

        // Real pass, part 1: postconditions first (their existing plan position),
        // with verified body asserts forwarded as assumptions.
        let mut postcondition_assumptions = verified_post_loop_facts.clone();
        postcondition_assumptions.extend(forwarded_body_asserts.iter().copied());
        let postcondition_slices = VerificationSlices::new(
            ctx,
            &plan.assumptions,
            &plan.broadcast_assumptions,
            &always_available_invariants,
            &postcondition_assumptions,
            &[],
        );
        if let Some(result) = verify_regular_assertions(
            &postcondition_slices,
            &postconditions,
            post_loop_modified_vars.as_ref(),
            false,
        ) {
            return result;
        }

        // Real pass, part 2: every other obligation, in original order.
        //
        // ── Sequential body-assert carry-forward ───────────────────────────
        // Verus carries each proven straight-line fact forward to subsequent
        // proof steps. trust-vc previously checked every body assert against the
        // SAME fixed assumption set (requires + assert_by + loop ensures), so an
        // earlier verified body assert was NOT visible to a later one — breaking
        // the canonical `assert(a =~= b); assert(a === b)` pattern (the proven
        // extensional equality was unavailable to the following strict-eq step).
        //
        // Passing `carry_forward = true` makes `verify_regular_assertions` thread
        // each VERIFIED forwardable body assert into the `verified_assert_by`
        // assumption slot for the assertions that follow it, in plan order.
        //
        // SOUNDNESS: identical to the #2778 postcondition-forwarding argument. A
        // body assert inside `if c { … }` is lowered to the path-guarded obligation
        // `c ==> assert` (#2779), so a VERIFIED body assert holds UNCONDITIONALLY
        // under the requires — the guard is folded into the proven fact, not
        // dropped. Forwarding that already-proven, unconditional (guard-folded)
        // fact as an assumption to a LATER obligation is sound modus-ponens, and
        // the strict left-to-right accumulation (only earlier→later, only after the
        // earlier step actually verified, short-circuiting on the first failure)
        // admits no circular reasoning. It can only ADD true hypotheses, so it
        // never turns a genuine failure into a spurious pass.
        let non_postcondition_slices = VerificationSlices::new(
            ctx,
            &plan.assumptions,
            &plan.broadcast_assumptions,
            &always_available_invariants,
            &verified_post_loop_facts,
            &[],
        );
        if let Some(result) = verify_regular_assertions(
            &non_postcondition_slices,
            &non_postcondition_assertions,
            post_loop_modified_vars.as_ref(),
            true,
        ) {
            return result;
        }

        // Recommends assertions: violations produce warnings, not failures.
        // Checked after regular assertions so hard failures take precedence.
        // Part of #2483.
        for recommends in &plan.recommends {
            let step = verification_report::begin_obligation_step(
                VerificationPhase::Recommendation,
                recommends,
            );
            let start = Instant::now();
            let slices = VerificationSlices::new(
                ctx,
                &plan.assumptions,
                &plan.broadcast_assumptions,
                &always_available_invariants,
                &verified_post_loop_facts,
                &[],
            );
            let recommends_result =
                Self::verify_typed_step(&slices, &[], recommends, post_loop_modified_vars.as_ref());
            verification_report::end_step_with_assertion_result(
                step,
                &recommends_result,
                start.elapsed(),
            );
            match recommends_result {
                Ok(AssertionOutcome::Verified) => {}
                Ok(AssertionOutcome::Counterexample {
                    obligation_name,
                    model,
                    ..
                }) => {
                    let loc = recommends.location.as_deref().unwrap_or("unknown location");
                    eprintln!(
                        "warning: recommends violation: {} at {}{}",
                        obligation_name,
                        loc,
                        model
                            .as_ref()
                            .map(|m| format!(" (model: {m})"))
                            .unwrap_or_default(),
                    );
                }
                Ok(AssertionOutcome::Unknown { reason, .. }) => {
                    eprintln!("warning: recommends check inconclusive: {reason}");
                }
                Ok(AssertionOutcome::Error { message }) => {
                    eprintln!("warning: recommends check error: {message}");
                }
                Err(err) => {
                    eprintln!("warning: recommends check error: {err}");
                }
            }
        }

        if vacuous_precheck_diagnostics.has_demoting() {
            demoted_context_result("typed verification context", &vacuous_precheck_diagnostics)
        } else {
            VerifyResult::Verified
        }
    }

    /// Verifies one typed assertion and keeps infrastructure failures on the
    /// `TrustVcError` channel until the outer boundary. Part of #1690, #2448.
    /// WF1 non-negativity FLOOR for a `loop_decreases!` measure.
    ///
    /// Proves `Inv(s) && G(s) |= M(s) >= 0` as a DIRECT single-state entailment,
    /// NEVER as an inductive step (which would vacuously assume the floor at the
    /// pre-state under a negative invariant — the quarantined hole). Mechanics:
    ///
    /// - The loop-modified variables are HAVOC'd via `post_loop_modified_vars`,
    ///   so every pre-loop entry fact about them (e.g. `requires(i < 0)`) is
    ///   forgotten and the floor must hold at an ARBITRARY loop head, not only at
    ///   loop entry.
    /// - The verified loop invariants are assumed at the current state (via the
    ///   `verified_invariants` slice).
    /// - The loop guard is assumed TRUE at the current state (a floor is a
    ///   property of every loop head at which the body is about to run). It is
    ///   carried in the SCOPED-assumptions slot so setup encodes it at the
    ///   current state and never pre-state-rewrites it under the havoc.
    /// - The floor is checked in the measure's OWN (native) sort — an `int`
    ///   measure stays a mathematical `int` (`i >= 0` genuinely refutable, never
    ///   the vacuous unsigned `>= 0`); a `u64` measure stays `Uint` (its floor is
    ///   0, and an exec expression that underflows, e.g. `5u64 - i`, is caught by
    ///   the assertion path's OVERFLOW pass — redundant belt-and-suspenders). The
    ///   `MeasureNonNegative` kind force-enables `use_int_for_measures`, which
    ///   would re-type EVERY var to `Int` and (a) over-reject a `u64` measure
    ///   whose floor is the implicit unsigned bound, and (b) leak `MathInt` into
    ///   the Uint-typed post-loop assumption — so the floor is verified through a
    ///   clone re-keyed to `Assert`, keeping native sorts and confining any
    ///   int-mode strictly out of the post-loop normal-exit path.
    /// - The auto-generated post-loop normal-exit fact (`PostLoopAssume`,
    ///   `!(guard)`) is EXCLUDED: it is a current-state EXIT fact that both
    ///   directly contradicts the guard-TRUE assumption (vacuously discharging the
    ///   floor) and, being Uint-typed, would clash with an int measure's sort.
    ///
    /// Returns `Some(terminal_result)` on Counterexample / Unknown / Error and
    /// `None` when the floor verified (the caller continues to the next measure).
    fn verify_measure_nonneg_floor(
        ctx: &PreparedVerificationContext,
        plan: &VerificationPlan<'_>,
        measure: &PreparedObligation,
        verified_invariants: &[&PreparedObligation],
    ) -> Option<VerifyResult> {
        let step =
            verification_report::begin_obligation_step(VerificationPhase::LoopDecreases, measure);
        let start = Instant::now();

        // Verify the floor in the measure's NATIVE sort. Re-key the obligation to
        // `Assert` so the assertion path does NOT force `use_int_for_measures`
        // (which re-types every var to `Int`): an `int` measure keeps `MathInt`
        // (refutable), a `u64` measure keeps `Uint` (floor 0 + overflow pass).
        let mut floor = measure.clone();
        floor.kind = ObligationKind::Assert;

        // Havoc the loop-modified variables (entry facts about them forgotten).
        // `classify_obligations` only routes an obligation here when its name is
        // registered in `loop_modified_vars`, so this is always `Some`.
        let modified: HashSet<String> = ctx
            .loop_modified_vars
            .get(&measure.name)
            .map(|vars| vars.iter().cloned().collect())
            .unwrap_or_default();

        // EXCLUDE the post-loop normal-exit fact (`!(guard)`): it is a
        // current-state EXIT fact that contradicts the guard-TRUE assumption
        // (which would vacuously discharge the floor) and is Uint-typed.
        let floor_assumptions: Vec<&PreparedObligation> = plan
            .assumptions
            .iter()
            .copied()
            .filter(|obligation| obligation.kind != ObligationKind::PostLoopAssume)
            .collect();

        // Assume the loop guard TRUE at the current state. The file path stores a
        // loop's guard as a STRING in `ctx.loop_guards` (keyed on this measure's
        // obligation name, registered alongside its loop metadata) — NOT as a
        // `LoopGuard` obligation, so `plan.loop_guards` is empty here. Lower the
        // guard string in the measure's variable environment; if it cannot be
        // lowered the floor is proven under the invariants alone, which is
        // conservative (it can only UNDER-verify, never false-verify). Carried in
        // the SCOPED-assumptions slot so setup encodes it at the current state
        // (never pre-state-rewritten under the havoc).
        let guard_condition = ctx.loop_guards.get(&measure.name);
        let guard_true = guard_condition
            .and_then(|condition| {
                Self::lower_measure_guard(ctx, condition).map(|expr| (condition, expr))
            })
            .map(|(condition, expr)| PreparedObligation {
                name: format!("{}_measure_floor_guard", measure.name),
                kind: ObligationKind::Assume,
                location: measure.location.clone(),
                condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
                bound_vars: None,
                trigger_patterns: None,
                prepared_triggers: None,
                solver_mode: None,
                is_opaque: false,
                is_inline: false,
                broadcast_group: None,
                condition: condition.clone(),
                expr,
                invariant_namespace: None,
                trigger_inference_mode: None,
                broadcast_guard: None,
                raw_broadcast_guard_count: 0,
                step_meta: None,
            });
        let mut guard_scope: Vec<&PreparedObligation> = Vec::new();
        if let Some(ref guard) = guard_true {
            guard_scope.push(guard);
        }

        let slices = VerificationSlices::new(
            ctx,
            &floor_assumptions,
            &plan.broadcast_assumptions,
            verified_invariants,
            &[],
            &guard_scope,
        );
        let result = Self::verify_typed_step(&slices, &[], &floor, Some(&modified));
        verification_report::end_step_with_assertion_result(step, &result, start.elapsed());
        match result {
            Ok(AssertionOutcome::Verified) => None,
            Ok(AssertionOutcome::Counterexample {
                model, bindings, ..
            }) => {
                let obligation_name = format!("{} (non-negative)", measure.display_name());
                Some(VerifyResult::Counterexample {
                    obligation_name,
                    location: measure.location.clone(),
                    model,
                    bindings,
                })
            }
            Ok(AssertionOutcome::Unknown {
                reason, category, ..
            }) => Some(VerifyResult::unknown(reason, category)),
            Ok(AssertionOutcome::Error { message }) => Some(VerifyResult::Error { message }),
            Err(err) => Some(VerifyResult::from(err)),
        }
    }

    /// Lowers a loop guard condition string to a `TrustVcExpr` in the measure's
    /// current-state variable environment, for the WF1 non-negativity floor.
    /// Returns `None` if the string cannot be parsed or lowered (the floor is
    /// then proven under the invariants alone — conservative, never a
    /// false-verify).
    fn lower_measure_guard(
        ctx: &PreparedVerificationContext,
        guard_condition: &str,
    ) -> Option<TrustVcExpr> {
        let mut env = TypeEnv::new();
        for var in &ctx.variables {
            env.insert(var.name.clone(), var.ty.clone());
        }
        let syn_expr: syn::Expr = syn::parse_str(guard_condition).ok()?;
        lower_syn_expr(&syn_expr, &env).ok()
    }

    fn verify_typed_step(
        slices: &VerificationSlices<'_>,
        extra_variables: &[crate::vc::VariableDecl],
        assertion: &PreparedObligation,
        post_loop_modified_vars: Option<&HashSet<String>>,
    ) -> TrustVcResult<AssertionOutcome> {
        // REFLEXIVE-DISEQUALITY REFUTATION (SOUNDNESS-CRITICAL on this lane).
        //
        // `verify_typed_step` is the shared lane for every obligation that is
        // NOT a regular assertion: the loop-invariant base case, loop `ensures`,
        // `assert ... by` conclusions AND their scoped assertions, the
        // postcondition-forwarding pre-pass, `recommends`, and the WF1
        // non-negativity floor. Its whole post-processing is
        // `apply_vacuity_probe_to_result` — the hypothesis-robust demote that
        // `typed_assertions::finish_regular_assertion_step` applies to the
        // regular lane never ran here. A DIRECT, unsound `Verified` for
        // `a != a` (the datatype-eq depth-1 UNSAT hole) was therefore taken at
        // face value on all of them, and on four of them a `Verified` is
        // EXPORTED as an assumption for every later obligation — an injected
        // contradiction with a wider blast radius than the pre-pass hole.
        //
        // Deciding it here, BEFORE the solver, closes all of those lanes with
        // one guard and simultaneously deletes the solve (this shape is the most
        // expensive obligation in the unit — ay does not converge on the negated
        // goal and the retry cascade runs it three times). It cannot make
        // anything verify: `reflexive_disequality_refutation` returns a
        // Counterexample or nothing at all.
        //
        // `by(compute)` keeps its own path: an assert_by conclusion in compute
        // mode is dispatched by the CALLER (`verify_compute_mode_obligation`)
        // and a compute-mode regular assert never reaches this function at all
        // (`verify_regular_assertions` handles `SolverMode::Compute` itself).
        // For the one shape that DOES reach here in compute mode — a compute
        // scoped assertion inside an assert_by, which has no caller-side
        // dispatch today — concrete evaluation of `a != a` returns `false`, i.e.
        // the same refutation, so no verdict moves.
        if let Some(outcome) = super::typed_assertions::reflexive_disequality_refutation(assertion)
        {
            return Ok(outcome);
        }
        let result = verify_single_assertion_typed_with_extra_variables(
            slices,
            assertion,
            post_loop_modified_vars,
            extra_variables,
        );
        // Vacuity gate (SOUNDNESS-CRITICAL): covers every goal that
        // flows through the typed step — assert_by! (and assert_by! with a
        // let-bound local), loop invariant base case, and loop ensures. A
        // #[broadcast] lemma or a trait-method `ensures` axiom can publish a
        // contradictory premise that proves any of these vacuously; if the goal
        // verified only because those premises are contradictory, downgrade it
        // to Unknown(VacuousTruth).
        // `extra_variables` (forall bound vars) are forwarded so the negated
        // probe is skolemized identically to the goal.
        super::assertion::apply_vacuity_probe_to_result(
            result,
            slices,
            assertion,
            extra_variables,
            post_loop_modified_vars,
        )
    }
}

/// Converts a typed verification step into the public compatibility result.
///
/// `None` means the step verified and the caller should continue checking
/// later obligations; `Some` carries the first public-facing terminal
/// result. Part of #1690. Made `pub(super)` for use by `typed_assertions`.
pub(super) fn finish_typed_step(result: TrustVcResult<AssertionOutcome>) -> Option<VerifyResult> {
    match result {
        Ok(AssertionOutcome::Verified) => None,
        Ok(outcome) => Some(outcome.into()),
        Err(err) => Some(VerifyResult::from(err)),
    }
}

#[cfg(test)]
#[path = "typed_tests.rs"]
mod tests;
