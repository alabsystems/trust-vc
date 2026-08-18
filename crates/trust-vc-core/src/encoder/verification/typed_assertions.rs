//! Regular assertion verification with shared-BV encoder reuse.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from `typed.rs` to keep file sizes under the 500-line limit.
//! Contains the shared-BV fast path logic and compute-mode dispatch for
//! regular assertions. Part of #2621.

use std::collections::HashSet;
use std::time::Instant;

use super::assertion::{
    can_use_shared_bv_fast_path, convert_setup_error, verify_assertion_with_shared_bv_encoder,
    verify_single_assertion_typed_with_extra_variables, SharedBvFastPathAttempt,
};
use super::outcome::AssertionOutcome;
use super::split::try_localize_failure;
use super::typed::finish_typed_step;
use super::unknown_category::UnknownCategory;
use super::VerificationSlices;
use crate::encoder::types::VerifyResult;
use crate::encoder::AYEncoder;
use crate::error::TrustVcResult;
use crate::prepared_context::PreparedObligation;
use crate::vc::SolverMode;
use crate::verification_report::{self, VerificationPhase};

/// Default shared-BV reuse batch limit (#2544): the ay-dpll incremental solver
/// accumulates internal state across push/pop cycles. After ~13 reuses
/// the BV decompose preprocessing degrades from ~240ms to >500ms per
/// check_sat, causing quadratic scaling. Rebuilding the encoder every
/// N assertions resets the solver state while still amortizing setup
/// cost within each batch.
const DEFAULT_SHARED_BV_REUSE_BATCH_LIMIT: usize = 8;

/// Returns the shared-BV reuse batch limit. In test builds, the limit
/// can be overridden via `TRUST_VC_SHARED_BV_REUSE_BATCH_LIMIT` env var
/// for benchmarking different reuse strategies (#2648).
fn shared_bv_reuse_batch_limit() -> usize {
    #[cfg(test)]
    {
        std::env::var("TRUST_VC_SHARED_BV_REUSE_BATCH_LIMIT")
            .ok()
            .and_then(|raw| raw.parse::<usize>().ok())
            .filter(|limit| *limit >= 1)
            .unwrap_or(DEFAULT_SHARED_BV_REUSE_BATCH_LIMIT)
    }

    #[cfg(not(test))]
    {
        DEFAULT_SHARED_BV_REUSE_BATCH_LIMIT
    }
}

/// Program point of a straight-line body obligation, derived from its name.
///
/// Body asserts/assumes are named `assertion_{N}` / `assumption_{N}` by
/// `body_extract` (`add_assertion` / `add_assumption`), where `N` is the single
/// monotonic extraction counter shared by both, advanced in source order. So the
/// `N` parsed here is a faithful program-order index for body asserts and body
/// assumes.
///
/// A conditionally/forward-established call's `ensures` is named
/// `__call_ensures_pp{N}_…`, where `N` is a program point reserved from the SAME
/// `next_assertion_index` counter at the call site (`add_helper_contract_
/// obligations`). Parsing it here makes a call's `ensures` order exactly like a
/// body `assume!` placed at the call site: `forward_visible_assumptions` hides it
/// from any body `assert!` at an earlier point, so an `assert!(P)` textually
/// before the call is not retroactively satisfied by the call's `ensures`.
///
/// A `while` loop's auto-generated normal-exit fact (the negated guard) is named
/// `post_loop_assumption_pp{N}`, where `N` is a program point reserved from the
/// SAME counter AFTER the loop body is visited (`add_post_loop_assumption`).
/// Parsing it here makes the exit fact order exactly like a body `assume!` placed
/// at the loop's normal-exit point: `forward_visible_assumptions` hides it from
/// any body `assert!` at an EARLIER point, so an `assert!(P)` textually BEFORE the
/// loop is not retroactively satisfied by the loop's exit fact, while a post-loop
/// `assert!` (a strictly-later point) still sees it (straight-line case preserved).
///
/// An exec arithmetic-safety / index-bounds obligation is named
/// `overflow_check_{N}` / `index_bounds_check_{N}`, where `N` is reserved from
/// the SAME `next_assertion_index` counter at the arithmetic site. A runtime
/// panic happens AT that program point, so only facts established EARLIER can
/// bear on it — most importantly, a `while` loop's normal-exit fact
/// (`post_loop_assumption_pp{N'}`, a strictly-LATER point) must NOT be visible to
/// a loop-BODY overflow check, or the exit hypothesis (`i < n` is false, i.e.
/// `n <= 0`) would vacuously discharge a genuine in-body overflow. Forward-
/// ordering these makes them see only earlier `assume!`s / call-`ensures`, which
/// is also strictly more sound for straight-line code (a later `assume!` can
/// never excuse an earlier arithmetic panic).
///
/// Every other obligation (the function `postcondition`, `precondition` /
/// requires, the call-site `__call_requires_*`, `return_value`, loop
/// invariants/ensures, …) has a different name shape and returns `None` — those
/// are not subject to forward-only ordering and stay unconditionally visible.
/// Part of the body `assume!` scope fix and its call-`ensures` / post-loop /
/// loop-body-arithmetic siblings.
fn body_program_point(name: &str) -> Option<usize> {
    if let Some(rest) = name
        .strip_prefix("__call_ensures_pp")
        .or_else(|| name.strip_prefix("__call_requires_pp"))
    {
        // `rest` is `{N}_{helper_name}_{call_index}_{index}`; the program point
        // is the leading run of digits up to the `_` separator. Rust function
        // names never start with a digit, so the `_` after `N` always bounds it.
        //
        // A call-site `requires` carries the SAME call-site program point as the
        // call's `ensures` (`__call_requires_pp{N}_…`). Forward-ordering it makes
        // `forward_visible_assumptions` hide a strictly-LATER body `assume!` /
        // call-`ensures` (point `>= N`) from the precondition check, so a later
        // fact cannot retroactively discharge an earlier precondition (round-8
        // findings 11/12); an EARLIER fact (point `< N`) is still visible.
        let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
        return digits.parse::<usize>().ok();
    }
    if let Some(rest) = name.strip_prefix("post_loop_assumption_pp") {
        // `rest` is exactly `{N}` (the reserved program point), so it parses
        // directly; the `take_while` keeps it robust to any future suffix.
        let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
        return digits.parse::<usize>().ok();
    }
    // `overflow_check_{N}` / `index_bounds_check_{N}` carry a trailing program
    // point reserved from the same counter; the `take_while` is robust to any
    // verification-time suffix appended to the stored name.
    if let Some(rest) = name
        .strip_prefix("overflow_check_")
        .or_else(|| name.strip_prefix("index_bounds_check_"))
    {
        let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
        return digits.parse::<usize>().ok();
    }
    let digits = name
        .strip_prefix("assertion_")
        .or_else(|| name.strip_prefix("assumption_"))?;
    digits.parse::<usize>().ok()
}

/// Forward-only assumption visibility for a body assertion (SOUNDNESS-CRITICAL).
///
/// A straight-line body `assert!` at program point `p` must be verified against
/// only the body `assume!`s established at an EARLIER point (`< p`), never a
/// later one — otherwise a textually-later `assume!(P)` would retroactively
/// satisfy an earlier `assert!(P)` (`assert!(b); assume!(b)` → false Verified).
///
/// Returns `Some(filtered)` when at least one assumption is dropped, and `None`
/// when nothing is removed — the overwhelmingly common case (no out-of-order
/// assume), in which the caller leaves the slice byte-identical and the shared-BV
/// fast path is fully preserved. Assumptions with no body program point
/// (requires/precondition, return_value, helper-call ensures, loop/post-loop
/// facts, …) are always retained, so non-`assume!` behavior is unchanged.
fn forward_visible_assumptions<'a>(
    assumptions: &[&'a PreparedObligation],
    assertion_name: &str,
) -> Option<Vec<&'a PreparedObligation>> {
    // An untagged assertion (postcondition / overflow check / measure / …) is
    // not part of the straight-line body order; it keeps the full assumption set
    // (a postcondition is checked at function exit and legitimately sees every
    // body assume). Only tagged body asserts are forward-filtered.
    let assert_point = body_program_point(assertion_name)?;
    let mut removed = false;
    let filtered: Vec<&'a PreparedObligation> = assumptions
        .iter()
        .copied()
        .filter(|assumption| match body_program_point(&assumption.name) {
            // A body assume at the same-or-later program point is not yet
            // established when this assert is checked. (Distinct obligations
            // never share a point, so this only ever drops strictly-later ones.)
            Some(assume_point) => {
                if assume_point >= assert_point {
                    removed = true;
                    false
                } else {
                    true
                }
            }
            None => true,
        })
        .collect();
    removed.then_some(filtered)
}

fn finish_reported_regular_assertion(
    step_index: Option<usize>,
    start: Instant,
    result: Option<VerifyResult>,
) -> Option<VerifyResult> {
    match result {
        Some(result) => {
            verification_report::end_step_with_verify_result(step_index, &result, start.elapsed());
            Some(result)
        }
        None => {
            verification_report::end_step_verified(step_index, start.elapsed());
            None
        }
    }
}

/// Verifies all regular assertions using the shared-BV fast path when
/// applicable, falling back to per-assertion encoders otherwise.
///
/// Returns `Some(result)` on the first terminal outcome (counterexample,
/// unknown, or error). Returns `None` if all assertions verify.
/// Part of #2621 (extracted from `verify_validated`).
///
/// When `carry_forward` is true, each VERIFIED forwardable body assert (see
/// `forwardable_body_assert`) is threaded into the `verified_assert_by`
/// assumption slot for the assertions that follow it, in stream order. This
/// implements sequential straight-line carry-forward (`assert(a =~= b);
/// assert(a === b)`): a fact proven earlier becomes a hypothesis for a later
/// step. Carry-forward applies only on the per-assertion fallback path (the
/// shared-BV fast path is reserved for non-collection scalar asserts and never
/// participates), so the cached shared-BV encoder is never invalidated by a
/// changing assumption set. SOUNDNESS: see the call-site note in `typed.rs` —
/// only already-verified, unconditional body asserts forward, strictly
/// earlier→later, so it can only add true hypotheses.
pub(super) fn verify_regular_assertions(
    slices: &VerificationSlices<'_>,
    assertions: &[&PreparedObligation],
    post_loop_modified_vars: Option<&HashSet<String>>,
    carry_forward: bool,
) -> Option<VerifyResult> {
    let mut shared_bv_encoder: Option<AYEncoder> = None;
    let mut shared_bv_fast_path_available = true;
    let mut shared_bv_reuse_count: usize = 0;
    // Verified forwardable body asserts accumulated so far (carry-forward).
    let mut carried_forward: Vec<&PreparedObligation> = Vec::new();

    for assertion in assertions {
        let step =
            verification_report::begin_obligation_step(VerificationPhase::Assertion, assertion);
        let start = Instant::now();

        // Forward-only assumption ordering (SOUNDNESS-CRITICAL): drop any body
        // `assume!` whose program point is not strictly before this body assert.
        // `None` (the common case: no out-of-order assume) leaves the slice
        // untouched, so the shared-BV fast path below stays eligible and the
        // common verification path is byte-identical to before.
        let forward_filtered = forward_visible_assumptions(slices.assumptions, &assertion.name);
        let active_slices_owned;
        let active_slices: &VerificationSlices<'_> = match &forward_filtered {
            Some(filtered) => {
                active_slices_owned = VerificationSlices {
                    assumptions: filtered.as_slice(),
                    ..*slices
                };
                &active_slices_owned
            }
            None => slices,
        };

        if let Some(mode) = assertion.solver_mode {
            match mode {
                SolverMode::Default | SolverMode::NonlinearArith | SolverMode::BitVector => {}
                SolverMode::Compute => {
                    match super::compute::try_compute_with_bindings(
                        &assertion.expr,
                        active_slices.assumptions,
                        active_slices.broadcast_assumptions,
                        active_slices.verified_assert_by,
                        &[],
                        &active_slices.ctx.revealed_fns,
                        &active_slices.ctx.hidden_fns,
                    ) {
                        Some(true) => {
                            verification_report::end_step_verified(step, start.elapsed());
                            continue;
                        }
                        Some(false) => {
                            let result = VerifyResult::Counterexample {
                                obligation_name: assertion.name.clone(),
                                model: Some(
                                    "by(compute): expression evaluates to false".to_string(),
                                ),
                                bindings: Vec::new(),
                            };
                            verification_report::end_step_with_verify_result(
                                step,
                                &result,
                                start.elapsed(),
                            );
                            return Some(result);
                        }
                        None => {
                            let result = VerifyResult::unknown(
                                format!(
                                    "Compute mode: '{}' contains symbolic variables \
                                     or expressions that cannot be fully evaluated. \
                                     by(compute) requires all values to be concrete.",
                                    assertion.name,
                                ),
                                None,
                            );
                            verification_report::end_step_with_verify_result(
                                step,
                                &result,
                                start.elapsed(),
                            );
                            return Some(result);
                        }
                    }
                }
                #[allow(unreachable_patterns)]
                _ => {
                    let result = VerifyResult::unknown(
                        format!(
                            "Unknown solver mode '{:?}' for '{}' — \
                             returning Unknown (fail-closed).",
                            mode, assertion.name,
                        ),
                        Some(UnknownCategory::UnsupportedMode),
                    );
                    verification_report::end_step_with_verify_result(
                        step,
                        &result,
                        start.elapsed(),
                    );
                    return Some(result);
                }
            }
        }

        // The shared-BV fast path caches one encoder across the batch, so it can
        // only run while the assumption set is the unfiltered, batch-wide slice.
        // A forward-filtered assert (`forward_filtered.is_some()`) drops to the
        // per-assertion fallback below, which rebuilds against `active_slices`.
        if forward_filtered.is_none()
            && shared_bv_fast_path_available
            && can_use_shared_bv_fast_path(
                assertion,
                slices.ctx.has_collection_context,
                super::assertion_bv_reuse::context_has_broadcast_use_marker(slices.ctx),
            )
        {
            if shared_bv_encoder.is_none() {
                match AYEncoder::setup_from_prepared(slices, false, post_loop_modified_vars) {
                    Ok(encoder) => shared_bv_encoder = Some(encoder),
                    Err(err) => {
                        if let Some(result) = finish_reported_regular_assertion(
                            step,
                            start,
                            finish_regular_assertion_step(
                                convert_setup_error(err),
                                slices,
                                assertion,
                                post_loop_modified_vars,
                            ),
                        ) {
                            return Some(result);
                        }
                        continue;
                    }
                }
            }

            if let Some(mut encoder) = shared_bv_encoder.take() {
                encoder.state.ground_pool.reset_flush_state();
                match verify_assertion_with_shared_bv_encoder(
                    slices,
                    assertion,
                    post_loop_modified_vars,
                    encoder,
                ) {
                    Ok(SharedBvFastPathAttempt::Reusable { encoder, outcome }) => {
                        shared_bv_reuse_count += 1;
                        if shared_bv_reuse_count >= shared_bv_reuse_batch_limit() {
                            drop(encoder);
                            shared_bv_reuse_count = 0;
                        } else {
                            shared_bv_encoder = Some(encoder);
                        }
                        // Demand-inline fall-through: the fast path has no
                        // retry cascade, so a fail-closed Unknown with inline
                        // candidates drops to the per-assertion fallback
                        // (which owns the demand-inline retry). See
                        // `unknown_should_fall_back_to_demand_inline`.
                        if !super::assertion::unknown_should_fall_back_to_demand_inline(
                            slices, assertion, &outcome,
                        ) {
                            if let Some(result) = finish_reported_regular_assertion(
                                step,
                                start,
                                finish_regular_assertion_step(
                                    Ok(outcome),
                                    slices,
                                    assertion,
                                    post_loop_modified_vars,
                                ),
                            ) {
                                return Some(result);
                            }
                            continue;
                        }
                    }
                    Ok(SharedBvFastPathAttempt::TimedOut) => {
                        shared_bv_fast_path_available = false;
                        shared_bv_reuse_count = 0;
                    }
                    Ok(SharedBvFastPathAttempt::NonReusable(outcome)) => {
                        shared_bv_reuse_count = 0;
                        if !super::assertion::unknown_should_fall_back_to_demand_inline(
                            slices, assertion, &outcome,
                        ) {
                            if let Some(result) = finish_reported_regular_assertion(
                                step,
                                start,
                                finish_regular_assertion_step(
                                    Ok(outcome),
                                    slices,
                                    assertion,
                                    post_loop_modified_vars,
                                ),
                            ) {
                                return Some(result);
                            }
                            continue;
                        }
                    }
                    Ok(SharedBvFastPathAttempt::Terminal(outcome)) => {
                        shared_bv_reuse_count = 0;
                        if !super::assertion::unknown_should_fall_back_to_demand_inline(
                            slices, assertion, &outcome,
                        ) {
                            if let Some(result) = finish_reported_regular_assertion(
                                step,
                                start,
                                finish_regular_assertion_step(
                                    Ok(outcome),
                                    slices,
                                    assertion,
                                    post_loop_modified_vars,
                                ),
                            ) {
                                return Some(result);
                            }
                            continue;
                        }
                    }
                    Err(err) => {
                        shared_bv_reuse_count = 0;
                        if let Some(result) = finish_reported_regular_assertion(
                            step,
                            start,
                            finish_regular_assertion_step(
                                Err(err),
                                slices,
                                assertion,
                                post_loop_modified_vars,
                            ),
                        ) {
                            return Some(result);
                        }
                        continue;
                    }
                }
            }
        }

        // Per-assertion fallback path. Carry-forward is applied HERE only: the
        // shared-BV fast path above is reserved for non-collection scalar asserts
        // (collection/ext-eq asserts always fall through to here), so its cached
        // encoder is never stale w.r.t. the growing assumption set.
        let combined_assert_by: Vec<&PreparedObligation>;
        let per_assertion_slices = if carry_forward && !carried_forward.is_empty() {
            combined_assert_by = active_slices
                .verified_assert_by
                .iter()
                .copied()
                .chain(carried_forward.iter().copied())
                .collect();
            VerificationSlices {
                verified_assert_by: combined_assert_by.as_slice(),
                ..*active_slices
            }
        } else {
            *active_slices
        };
        let per_assertion_slices = &per_assertion_slices;

        if let Some(result) = finish_reported_regular_assertion(
            step,
            start,
            finish_regular_assertion_step(
                verify_single_assertion_typed_with_extra_variables(
                    per_assertion_slices,
                    assertion,
                    post_loop_modified_vars,
                    &[],
                ),
                per_assertion_slices,
                assertion,
                post_loop_modified_vars,
            ),
        ) {
            return Some(result);
        }

        // Reached only when the assertion VERIFIED above (no terminal result was
        // returned). Carry it forward to later body asserts when it is a
        // forwardable, unconditional straight-line fact AND a collection
        // extensional equality — the only shape the strict-eq bridge consumes.
        // Scoping to that shape (rather than every verified body assert) keeps
        // unrelated facts (e.g. `choose`-bearing membership asserts) out of the
        // forwarded set, where they could degrade a later obligation's solver
        // outcome. See the soundness note at the `carry_forward = true` call site.
        if carry_forward
            && super::typed::forwardable_body_assert(assertion)
            && crate::extensional_eq::is_collection_extensional_eq(&assertion.expr)
        {
            carried_forward.push(*assertion);
        }
    }

    None
}

/// Gate for synthesizing a Counterexample from a compute-mode `Some(false)`
/// (SOUNDNESS-CRITICAL — guards against a FALSE counterexample on a TRUE claim).
///
/// Promoting a concrete `false` evaluation to a Counterexample is sound only when
/// the goal is a *bare, closed, ground* assertion: with NO constraining
/// hypotheses the context cannot be vacuously contradictory, so a ground term
/// that reduces to `false` is genuinely refutable (`⊨ ¬G`). Returns `true` iff:
///
///   * there are no user assumptions of ANY shape (regular, scoped, or verified
///     `assert_by`) — an equality assumption would have fed `build_compute_bindings`
///     and a non-equality assumption (`x > 5`) could constrain the value without
///     being visible to the evaluator, either of which could make `false` reflect
///     missing context rather than a genuine refutation;
///   * there are no verified loop invariants in scope (a loop invariant is itself a
///     constraining premise that could be vacuous); and
///   * no GENUINE `#[broadcast]` lemma is active — a bogus broadcast lemma can
///     publish a contradictory premise (the vacuity risk the broadcast-vacuity
///     probe guards on the Verified side); definitional `__body_axiom_<fn>`
///     assumptions are excluded (they are the function definitions the evaluator
///     unfolds and are consistent by construction).
///
/// A suppressed/ill-founded recursive fn never reaches this gate (its body is
/// absent from the compute catalog, so the evaluator returns `None`), and a goal
/// over a symbolic parameter likewise yields `None`.
fn goal_is_closed_ground(slices: &VerificationSlices<'_>) -> bool {
    slices.assumptions.is_empty()
        && slices.scoped_assumptions.is_empty()
        && slices.verified_assert_by.is_empty()
        && slices.verified_invariants.is_empty()
        && !super::assertion::context_has_broadcast_lemma(slices)
}

/// True iff `expr` is a top-level datatype (dis)equality goal — an `Eq`/`Ne`
/// comparison whose operands are datatype-valued (a built-in / user `enum`,
/// possibly recursive). Used to re-validate a *direct* SMT `Verified` for such a
/// goal against the concrete evaluator (SOUNDNESS-CRITICAL).
///
/// ay's native datatype theory case-splits constructors only at solver
/// scope-depth 0, but every obligation is discharged inside a `push` scope
/// (depth 1). For a datatype disequality `a != b` (lowered as `not(eq(a, b))`),
/// the verifier asserts the negation `eq(a, b)` and checks UNSAT; with the
/// constructor case-split unavailable at depth 1, ay can declare `eq(a, b)`
/// UNSOUNDLY UNSAT for a datatype-valued spec-fn-result operand, returning a
/// DIRECT (wrong) `Verified` — even for the tautologically-false `a != a`. The
/// `==` direction is unaffected: its negated goal `not(eq)` is left
/// `Unknown(Incompleteness)` and already routes to the compute recovery.
/// A `Compare { Ne, a, b }` whose operands are STRUCTURALLY IDENTICAL — `a != a`.
/// For a pure spec operand this is FALSE by reflexivity, INDEPENDENT of any
/// assumption context, so a `Verified` is unsound (the datatype-eq depth-1 UNSAT
/// hole surfaced under a hypothesis) UNLESS the context is vacuous. Demoting it
/// can only turn an unsound `Verified` into a Counterexample or, at worst,
/// over-reject a vacuous `a != a` (unsatisfiable context) — never a false-verify.
fn is_syntactic_self_disequality(expr: &crate::ir::TrustVcExpr) -> bool {
    matches!(
        expr,
        crate::ir::TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Ne,
            left,
            right,
        } if left == right
    )
}

fn is_datatype_eq_goal(expr: &crate::ir::TrustVcExpr) -> bool {
    fn ty_is_datatype(ty: &crate::ir::TrustVcType) -> bool {
        matches!(
            ty,
            crate::ir::TrustVcType::Datatype { .. } | crate::ir::TrustVcType::RecursiveRef(_)
        )
    }
    match expr {
        crate::ir::TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Eq | crate::ir::CompareOp::Ne,
            left,
            right,
        } => {
            ty_is_datatype(&crate::ir_lowering::infer_expr_type(left))
                || ty_is_datatype(&crate::ir_lowering::infer_expr_type(right))
        }
        _ => false,
    }
}

/// On counterexample: attempt to localize via assertion splitting.
/// Part of #2485.
fn finish_regular_assertion_step(
    result: TrustVcResult<AssertionOutcome>,
    slices: &VerificationSlices<'_>,
    assertion: &PreparedObligation,
    post_loop_modified_vars: Option<&HashSet<String>>,
) -> Option<VerifyResult> {
    // Vacuity gate (SOUNDNESS-CRITICAL): a #[broadcast] lemma OR a trait-method
    // `ensures` can publish a contradictory premise that proves a regular
    // assert! / postcondition vacuously — for a trait contract the premise can
    // even be UNREALIZABLE (`ensures(result > x)` over u32 has no solution at
    // u32::MAX), under which BOTH a claim and its negation reported Verified.
    // If the goal verified only because those premises are contradictory,
    // downgrade it to Unknown(VacuousTruth).
    // Regular asserts carry no forall bound vars, so extra_variables is empty.
    let result = super::assertion::apply_vacuity_probe_to_result(
        result,
        slices,
        assertion,
        &[],
        post_loop_modified_vars,
    );
    // Datatype (dis)equality direct-`Verified` re-validation (SOUNDNESS-CRITICAL).
    //
    // A datatype disequality goal `a != b` can be reported `Verified` DIRECTLY by
    // the SMT path via the unsound depth-1 `eq` UNSAT (see `is_datatype_eq_goal`),
    // even when it is genuinely false (e.g. `dbl(1) != dbl(1)`). A direct `Verified`
    // short-circuits the `Incompleteness` compute recovery below (which only fires
    // on `Unknown`), so the bare-`!=` hole would never be refuted. This runs BEFORE
    // `finish_typed_step` (which collapses `Verified` to `None`): re-check a
    // *closed/ground* datatype (dis)equality goal that the SMT reported `Verified`
    // against the same concrete evaluator the recovery trusts; when it reduces the
    // goal to `false`, demote the outcome to a Counterexample (the SMT `Verified`
    // was the unsound one).
    //
    // SOUNDNESS: gated by `goal_is_closed_ground` exactly like the refutation
    // recovery below — the entire user-assumption context must be empty, so a
    // ground goal that concretely evaluates to `false` is genuinely refutable
    // (`⊨ ¬G`). A genuinely TRUE datatype `!=` computes to `true` (the override
    // does nothing, the `Verified` is preserved); a SYMBOLIC operand makes the
    // evaluator return `None` (the override does nothing); and a goal under ANY
    // hypothesis fails `goal_is_closed_ground` (its `Verified` may legitimately
    // rest on that hypothesis and is preserved). It can only turn an UNSOUND
    // `Verified` into a Counterexample, never a true `Verified` into a failure.
    let result = match &result {
        // HYPOTHESIS-ROBUST reflexive-disequality demote. `a != a` (structurally
        // identical operands) is false by reflexivity regardless of the
        // assumption context, so unlike the closed-ground compute recovery below
        // it fires even under a hypothesis — closing the datatype-eq hole that
        // `assume!(m==0); assert!(dbl(x) != dbl(x))` reached by defeating
        // `goal_is_closed_ground`. Sound (never a false-verify; at worst
        // over-rejects a vacuous `a != a`).
        Ok(AssertionOutcome::Verified) if is_syntactic_self_disequality(&assertion.expr) => {
            Ok(AssertionOutcome::Counterexample {
                obligation_name: assertion.name.clone(),
                model: Some(
                    "reflexive disequality `a != a` is false (hypothesis-robust)".to_string(),
                ),
                bindings: Vec::new(),
            })
        }
        Ok(AssertionOutcome::Verified)
            if goal_is_closed_ground(slices)
                && is_datatype_eq_goal(&assertion.expr)
                && super::compute::try_compute_with_bindings(
                    &assertion.expr,
                    slices.assumptions,
                    slices.broadcast_assumptions,
                    slices.verified_assert_by,
                    slices.scoped_assumptions,
                    &slices.ctx.revealed_fns,
                    &slices.ctx.hidden_fns,
                ) == Some(false) =>
        {
            Ok(AssertionOutcome::Counterexample {
                obligation_name: assertion.name.clone(),
                model: Some(
                    "concrete datatype refutation: closed ground (dis)equality goal \
                     evaluates to false"
                        .to_string(),
                ),
                bindings: Vec::new(),
            })
        }
        _ => result,
    };

    let result = finish_typed_step(result)?;

    // Concrete-compute recovery for an Unknown solver outcome.
    //
    // ay's native datatype theory case-splits constructors only in its eager
    // pipeline, which runs solely at solver scope-depth 0; trust-vc discharges
    // every obligation inside a `push` scope (depth 1). A datatype tester on a
    // value bound by an in-scope equality to a *nullary* constructor constant
    // (e.g. postcondition `result.is_Left()` with assumption
    // `result == Direction::Left`) therefore degrades to Unknown(Incompleteness)
    // — the native-datatype-migration regression. Constructor *applications*
    // like `Green(7)` carry a syntactic constructor leaf the theory resolves, so
    // only bare nullary constants hit this.
    //
    // `try_compute_with_bindings` substitutes the in-scope equality bindings into
    // the obligation and evaluates it on fully concrete datatype values. It
    // unfolds the SAME defining body the SMT axiom encodes
    // (`build_compute_body_catalog`), so its verdict is congruent with the
    // solver's intended semantics:
    //
    //   * `Some(true)`  — UPGRADE the Unknown to Verified (close the incompleteness).
    //   * `Some(false)` — synthesize a Counterexample (the completeness DUAL of the
    //                     upgrade), but ONLY for a CLOSED/GROUND goal in a context
    //                     with no constraining hypotheses (see `goal_is_closed_ground`).
    //   * `None`        — symbolic residue / suppressed body / recursion-limit; keep
    //                     the fail-closed Unknown.
    //
    // We never override a Verified, and never synthesize a *Verified* from compute.
    // Mirrors the nonlinear-real certificate upgrade in assertion.rs.
    //
    // SOUNDNESS (false-counterexample is the critical risk). A `Some(false)` is only
    // promoted to a Counterexample under `goal_is_closed_ground`, which requires the
    // ENTIRE user-assumption context to be empty (no regular/scoped/assert_by
    // assumptions, no verified loop invariants) AND no genuine `#[broadcast]` lemma
    // in scope. With no constraining hypotheses the goal cannot be vacuously true,
    // so a ground term that concretely evaluates to `false` is GENUINELY refutable
    // (`⊨ ¬G`). The evaluator returns `Some(false)` only after fully reducing the
    // ground term within its recursion bound; a SUPPRESSED/ill-founded recursive fn
    // is absent from the body catalog (`eval` → `None`, no fabricated cex), and a
    // SYMBOLIC scrutinee makes `eval_match` return `None` (the gate never fires).
    //
    // Scoped to the `Incompleteness` category — the precise class of the
    // datatype-theory scope-depth gap — so the recovery never papers over an
    // unrelated solver panic / encoding error (those keep their original
    // fail-closed Unknown).
    // Matches BOTH inconclusive shapes carrying the `Incompleteness` category.
    // An incompleteness on a proof obligation now surfaces as `NotProved`
    // (`docs/design-unknown-as-failure.md`); this recovery must still run
    // BEFORE that failure is reported, exactly as it did when the same outcome
    // was spelled `Unknown { category: Incompleteness }`. Missing the
    // `NotProved` arm here would silently disable the recovery and turn genuine
    // model-bearing refutations into model-less non-proofs.
    if matches!(
        result,
        VerifyResult::NotProved {
            category: UnknownCategory::Incompleteness,
            ..
        } | VerifyResult::Unknown {
            category: UnknownCategory::Incompleteness,
            ..
        }
    ) {
        match super::compute::try_compute_with_bindings(
            &assertion.expr,
            slices.assumptions,
            slices.broadcast_assumptions,
            slices.verified_assert_by,
            slices.scoped_assumptions,
            &slices.ctx.revealed_fns,
            &slices.ctx.hidden_fns,
        ) {
            Some(true) => return None,
            Some(false) if goal_is_closed_ground(slices) => {
                return Some(VerifyResult::Counterexample {
                    obligation_name: assertion.name.clone(),
                    model: Some(
                        "concrete datatype refutation: closed ground goal evaluates to false"
                            .to_string(),
                    ),
                    bindings: Vec::new(),
                });
            }
            _ => {}
        }
    }

    if let VerifyResult::Counterexample { ref model, .. } = result {
        if let Some(localized) = verification_report::with_capture_suppressed(|| {
            try_localize_failure(slices, assertion, post_loop_modified_vars, model)
        }) {
            return Some(localized);
        }
    }

    Some(result)
}

#[cfg(test)]
mod forward_ordering_tests {
    use super::{body_program_point, forward_visible_assumptions};
    use crate::ir::TrustVcExpr;
    use crate::prepared_context::PreparedObligation;
    use crate::vc::{ConditionOrigin, ObligationKind};

    fn assumption(name: &str) -> PreparedObligation {
        PreparedObligation {
            name: name.to_string(),
            kind: ObligationKind::Assume,
            location: None,
            condition_origin: ConditionOrigin::LoweredFromCondition,
            bound_vars: None,
            trigger_patterns: None,
            prepared_triggers: None,
            solver_mode: None,
            is_opaque: false,
            is_inline: false,
            broadcast_group: None,
            condition: "true".to_string(),
            expr: TrustVcExpr::BoolLit(true),
            invariant_namespace: None,
            trigger_inference_mode: None,
            broadcast_guard: None,
            raw_broadcast_guard_count: 0,
            step_meta: None,
        }
    }

    #[test]
    fn body_program_point_parses_only_body_obligation_names() {
        assert_eq!(body_program_point("assertion_0"), Some(0));
        assert_eq!(body_program_point("assertion_42"), Some(42));
        assert_eq!(body_program_point("assumption_7"), Some(7));
        // Non-body obligations carry no program point and stay always-visible.
        assert_eq!(body_program_point("postcondition"), None);
        assert_eq!(body_program_point("precondition"), None);
        assert_eq!(body_program_point("return_value"), None);
        // Exec arithmetic-safety / index-bounds obligations ARE forward-ordered
        // by their reserved program point, so a loop-BODY overflow check does not
        // see the loop's strictly-later normal-exit fact (which would vacuously
        // discharge a genuine in-body overflow).
        assert_eq!(body_program_point("overflow_check_3"), Some(3));
        assert_eq!(body_program_point("index_bounds_check_5"), Some(5));
        // A call's ensures carries a reserved straight-line program point so it
        // orders like a body `assume!` placed at the call site.
        assert_eq!(body_program_point("__call_ensures_pp0_h_0_0"), Some(0));
        assert_eq!(
            body_program_point("__call_ensures_pp13_my_helper_2_1"),
            Some(13)
        );
        // A call-site precondition carries its call-site program point so a
        // strictly-LATER body `assume!`/call-`ensures` cannot retroactively
        // discharge it (round-8 findings 11/12).
        assert_eq!(body_program_point("__call_requires_pp0_h_0_0"), Some(0));
        assert_eq!(
            body_program_point("__call_requires_pp7_my_helper_2_1"),
            Some(7)
        );
        // A legacy/un-stamped requires/ensures name (no `pp` marker) carries no
        // point (kept for robustness against any future un-stamped emitter).
        assert_eq!(body_program_point("__call_requires_h_0_0"), None);
        assert_eq!(body_program_point("__call_ensures_h_0_0"), None);
        assert_eq!(body_program_point("assumption_"), None);
    }

    #[test]
    fn later_assume_is_dropped_for_earlier_assert() {
        // `assert!(b)` is assertion_0; the textually-later `assume!(b)` is
        // assumption_1. The assert must not see the later assume.
        let later = assumption("assumption_1");
        let assumptions: Vec<&PreparedObligation> = vec![&later];
        let filtered = forward_visible_assumptions(&assumptions, "assertion_0")
            .expect("a strictly-later assume must be filtered out");
        assert!(filtered.is_empty(), "later assume must be dropped");
    }

    #[test]
    fn earlier_assume_is_kept_for_later_assert() {
        // `assume!(x)` is assumption_0; the later `assert!(x)` is assertion_1.
        let earlier = assumption("assumption_0");
        let assumptions: Vec<&PreparedObligation> = vec![&earlier];
        // Nothing removed → None (slice left untouched, fast path preserved).
        assert!(forward_visible_assumptions(&assumptions, "assertion_1").is_none());
    }

    #[test]
    fn untagged_assertion_keeps_all_assumptions() {
        // A postcondition (untagged) sees every body assume, even a "later" one.
        let later = assumption("assumption_99");
        let assumptions: Vec<&PreparedObligation> = vec![&later];
        assert!(forward_visible_assumptions(&assumptions, "postcondition").is_none());
    }

    #[test]
    fn untagged_assumptions_are_never_dropped() {
        // requires/precondition + return_value remain visible regardless of the
        // assert's program point; only the strictly-later body assume is dropped.
        let precondition = assumption("precondition");
        let return_value = assumption("return_value");
        let later = assumption("assumption_5");
        let assumptions: Vec<&PreparedObligation> = vec![&precondition, &return_value, &later];
        let filtered = forward_visible_assumptions(&assumptions, "assertion_2")
            .expect("the later body assume must be filtered");
        let names: Vec<&str> = filtered.iter().map(|o| o.name.as_str()).collect();
        assert_eq!(names, vec!["precondition", "return_value"]);
    }
}
