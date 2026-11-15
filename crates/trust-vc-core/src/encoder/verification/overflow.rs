//! Overflow predicate checking for assertion and inductive-step verification.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::outcome::AssertionOutcome;
use super::panic::{is_ay_panic, is_sort_mismatch_error};
use super::solve::{
    classify_unknown_reason, format_solver_observation_error, format_unknown_reason,
    gate_relabelled_category, model_gate_rejection, render_model_gate_rejection,
    try_check_sat_with_details,
};
use super::unknown_category::UnknownCategory;
use crate::encoder::AYEncoder;
use crate::error::{TrustVcError, TrustVcResult};
use crate::verification_report;
use ay_dpll::api::SolverScope;

fn overflow_error(context: &'static str, detail: impl Into<String>) -> TrustVcError {
    TrustVcError::Encoding {
        context,
        detail: detail.into(),
    }
}

/// Run overflow predicate checks on a pre-configured encoder.
///
/// Resolves the assertion expression with overflow tracking enabled, then
/// checks each overflow predicate (e.g., addition overflow, shift bounds)
/// against the current solver context. Returns `AssertionOutcome::Verified`
/// when all checks pass and otherwise returns the matching overflow outcome.
///
/// Reusable across assertion and inductive step paths. The caller must
/// provide a fully configured encoder (variables declared, assumptions
/// loaded). Part of #2246.
pub(in crate::encoder) fn check_overflow_predicates(
    encoder: &mut AYEncoder,
    assertion: &crate::prepared_context::PreparedObligation,
    check_overflow: bool,
) -> TrustVcResult<AssertionOutcome> {
    #[cfg(test)]
    if super::test_hooks::FORCE_OVERFLOW_PRECHECK_DEMOTION.with(|flag| flag.get()) {
        encoder.state.diagnostics.record(
            crate::encoder::diagnostics::EncodingApproximation::FunctionContextReturnTypeOmitted,
        );
    }

    let saved_lengths = encoder.collection_lengths.clone();
    let overflow_result = crate::encoder::with_flag_unwind_safe!(
        encoder.state.active_solver_mode,
        assertion.solver_mode,
        { encoder.resolve_condition_overflow_with_const_fold(&assertion.expr, check_overflow) }
    );
    let (_, overflow_checks, const_fold_overflow) = match overflow_result {
        Ok(result) => result,
        Err(e) => {
            let msg = format!(
                "Failed to parse overflow checks for '{}': {}",
                assertion.name, e
            );
            if is_sort_mismatch_error(&e) {
                return Ok(AssertionOutcome::unknown(msg, None));
            }
            return Err(overflow_error("resolve overflow predicates", msg));
        }
    };
    encoder.collection_lengths = saved_lengths;

    // Constant-folded definite overflow verdicts are decided exactly in Rust at
    // encoding time (all-constant operands, known finite width), bypassing the
    // solver entirely. A `true` verdict is a sound counterexample; `false`
    // verdicts carry no obligation and are never recorded. This closes the
    // ay-dpll CEGQI gap where a fully-ground `bvadd_no_overflow`-style query
    // returns SAT with an empty model instead of a definite result (#2778).
    for (check_name, overflows) in &const_fold_overflow {
        debug_assert!(
            *overflows,
            "only definite-overflow verdicts should be recorded"
        );
        if *overflows {
            return Ok(AssertionOutcome::Counterexample {
                obligation_name: format!(
                    "{}: {} in '{}'",
                    assertion.display_name(),
                    check_name,
                    assertion.condition
                ),
                location: assertion.location.clone(),
                model: Some(format!(
                    "constant-folded overflow: '{}' overflows at a fixed-width \
                     operation with all-constant operands",
                    check_name
                )),
                bindings: Vec::new(),
            });
        }
    }

    for (check_name, predicate) in &overflow_checks {
        let mut scope = match SolverScope::new(&mut encoder.solver) {
            Ok(scope) => scope,
            Err(e) => {
                return Ok(AssertionOutcome::unknown(
                    format!(
                        "ay error creating solver scope for overflow check '{}' in '{}': {}",
                        check_name, assertion.name, e
                    ),
                    Some(UnknownCategory::SolverPanic),
                ));
            }
        };
        let negated = match scope.try_not(*predicate) {
            Ok(negated) => negated,
            Err(e) => {
                let msg = format!(
                    "Failed to negate overflow check '{}' in '{}': {}",
                    check_name, assertion.name, e
                );
                if is_ay_panic(&e.to_string()) {
                    return Ok(AssertionOutcome::unknown(
                        msg,
                        Some(UnknownCategory::SolverPanic),
                    ));
                }
                return Err(overflow_error("negate overflow predicate", msg));
            }
        };
        if let Err(e) = scope.try_assert_term(negated) {
            let msg = format!(
                "Failed to assert overflow check '{}' in '{}': {}",
                check_name, assertion.name, e
            );
            if is_ay_panic(&e.to_string()) {
                return Ok(AssertionOutcome::unknown(
                    msg,
                    Some(UnknownCategory::SolverPanic),
                ));
            }
            return Err(overflow_error("assert overflow predicate", msg));
        }

        let details = match try_check_sat_with_details(&mut scope, &mut encoder.state.solver_panic)
        {
            Ok(details) => details,
            Err(error) => {
                return Ok(AssertionOutcome::unknown(
                    format_solver_observation_error(
                        format!(
                            "ay error during overflow check '{}' in '{}'",
                            check_name, assertion.name
                        ),
                        error,
                    ),
                    Some(UnknownCategory::SolverPanic),
                ));
            }
        };
        tracing::debug!(
            assertion = %assertion.name,
            overflow_check = %check_name,
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
            term_bytes = scope.instance_term_bytes(),
            "overflow check solver stats"
        );
        verification_report::record_solve_details(&details, Some(scope.instance_term_bytes()));
        let solve_result = details.result.result();
        if solve_result.is_unsat() {
            // Overflow check passed — predicate holds under all models.
        } else if solve_result.is_sat() {
            if !details.verification.sat_model_validated {
                return Ok(AssertionOutcome::unknown(
                    format!(
                        "sat model not validated by ay for overflow check \
                             '{}' in '{}'",
                        check_name, assertion.name
                    ),
                    Some(UnknownCategory::ModelNotValidated),
                ));
            }
            let obligation_name = format!(
                "{}: possible {} in '{}'",
                assertion.display_name(),
                check_name,
                assertion.condition
            );
            // Diagnostic-parity (#2778): an exec bit-shift whose shift amount has
            // a *signed* type is possibly negative, so the `0 <= b < width`
            // obligation is undischargeable. Upstream Verus surfaces this as a
            // VIR-level error (`assert_vir_error_msg`, no diagnostic code) rather
            // than an `assert_fails` counterexample. The solver obligation here is
            // identical to every other shift bound check — only the *out-of-range*
            // SAT failure is reclassified to `VerifyResult::Error`, so a
            // provably-in-range signed amount still verifies (UNSAT -> Verified)
            // and an out-of-range one still fails closed. The check name carries
            // the byte-exact upstream label, so this reproduces
            // `possible bit shift underflow/overflow` verbatim. Unsigned over-shift
            // checks (`left shift overflow` / `right shift overflow`) keep their
            // counterexample classification, matching upstream `assert_fails`.
            //
            // This reclassification runs BEFORE the empty-model guard below: the
            // refutation is already decisive here (SAT + `sat_model_validated`),
            // and ay-dpll's CEGQI cannot always *render* a concrete shift-amount
            // witness for the negated bound (it returns SAT with an empty model).
            // Without this ordering, the byte-exact upstream Error would sink into
            // an `EmptyModel` Unknown for the literal exec bodies
            // `let z = x << y;` with `y: iN` possibly-negative (upstream
            // `bit_shift_underflow`, `bit_shift_unsigned_shift_signed`). Soundness
            // is unchanged: a provably-in-range amount is UNSAT -> Verified above,
            // so this only fires on a genuinely refuted (validated-SAT) shift.
            if check_name.contains("bit shift underflow/overflow") {
                return Ok(AssertionOutcome::Error {
                    message: obligation_name,
                });
            }
            let model = match scope.try_get_model() {
                Ok(model) => Some(model),
                Err(e) => {
                    return Ok(AssertionOutcome::unknown(
                        format!(
                            "ay error getting model for overflow check '{}' in '{}': {}",
                            check_name, assertion.name, e
                        ),
                        Some(UnknownCategory::SolverPanic),
                    ));
                }
            };
            if model.as_ref().is_none_or(|m| m.model().is_empty()) {
                // Diagnostic-parity (#2778): a *constant* unsigned over-shift
                // (e.g. `1u8 << 9`, `255u8 >> 9`) has no free variable, so
                // ay-dpll CEGQI returns SAT with an empty model — there is
                // nothing to assign. The validated-SAT refutation is decisive
                // regardless: the shift obligation is `shift_amount < width`
                // (`bvult`, see `operators::check_shift_overflow`); negating it
                // and finding (validated) SAT means the ground shift amount is
                // `>= width`, exactly the over-shift UB upstream Verus rejects
                // via `assert_fails` for `left shift overflow` /
                // `right shift overflow`. A provably-in-range constant shift is
                // UNSAT -> Verified above and never reaches here, so this fires
                // ONLY on a genuine over-shift witness (never on a valid shift).
                // This mirrors the signed `bit shift underflow/overflow`
                // reclassification above but keeps the unsigned `assert_fails`
                // counterexample verdict (not the signed `assert_vir_error_msg`
                // Error). The free-variable over-shift case keeps its rich
                // model-rendered counterexample below; only the empty-model
                // ground case is rescued here — without this it would sink into
                // an `EmptyModel` Unknown. Non-shift overflow checks are
                // untouched: their definite ground overflows are decided by the
                // const-fold path above, so they never depend on this branch.
                if check_name.contains("left shift overflow")
                    || check_name.contains("right shift overflow")
                {
                    return Ok(AssertionOutcome::Counterexample {
                        obligation_name,
                        location: assertion.location.clone(),
                        model: Some(format!(
                            "constant over-shift: shift amount is >= the bit width \
                             ('{}'); no free variable to assign",
                            check_name
                        )),
                        bindings: Vec::new(),
                    });
                }
                // Diagnostic-parity (#2778): a *ground* out-of-bounds Seq element
                // index (e.g. `Seq::<int>::new(5, f).index(5)`, `.index(7)`) has
                // no free variable — the whole sequence is a constant construction
                // — so ay-dpll CEGQI returns SAT with an empty model for the
                // negated bound: there is nothing to assign. The validated-SAT
                // refutation is decisive regardless. The Seq element-index
                // obligation built by `add_seq_index_bounds_check` is
                // `0 <= i && i < len` (Route A Int form) or `i <u len` (legacy BV
                // form); negating it and finding (validated) SAT means the ground
                // index is `>= len` (or negative), exactly the out-of-bounds Seq
                // access upstream Verus rejects as `index requires i < len`. A
                // provably-in-range index makes the bound ground-TRUE, so its
                // negation is UNSAT — decided as Verified above, never reaching
                // this branch; and a Seq with a *free* variable yields a non-empty
                // model and keeps its rich model-rendered counterexample below.
                // So this fires ONLY on a genuine ground OOB index, mirroring the
                // unsigned over-shift reclassification above. The label gate is the
                // element-index precondition string (`requires i < len` for the
                // index/get/update bound, `requires 0 <= i < len` for the native
                // form) — it does NOT match the Seq length-prefix bounds
                // (`take`/`skip`/`subrange`, which read `requires n <= len` /
                // `requires end <= len`) nor any non-Seq overflow check, whose
                // definite ground violations are decided by the const-fold path
                // above. Without this, the byte-exact OOB failure would sink into
                // an `EmptyModel` Unknown.
                if check_name.contains("requires i < len")
                    || check_name.contains("requires 0 <= i < len")
                {
                    return Ok(AssertionOutcome::Counterexample {
                        obligation_name,
                        location: assertion.location.clone(),
                        model: Some(format!(
                            "out-of-bounds Seq index: index is >= len (or negative) \
                             for a constant Seq ('{}'); no free variable to assign",
                            check_name
                        )),
                        bindings: Vec::new(),
                    });
                }
                return Ok(AssertionOutcome::unknown(
                    format!(
                        "Solver returned SAT with empty model for overflow check \
                             '{}' in '{}' — treating as unknown (ay-dpll CEGQI limitation)",
                        check_name, assertion.name
                    ),
                    Some(UnknownCategory::EmptyModel),
                ));
            }
            let model_str = model.as_ref().map(|m| {
                super::model_render::format_counterexample_model(
                    m,
                    &encoder.var_types,
                    &encoder.counterexample_var_meta,
                )
            });
            let bindings = model
                .as_ref()
                .map(|m| {
                    super::model_render::collect_counterexample_bindings(
                        m,
                        &encoder.var_types,
                        &encoder.counterexample_var_meta,
                    )
                })
                .unwrap_or_default();
            return Ok(AssertionOutcome::Counterexample {
                obligation_name,
                location: assertion.location.clone(),
                model: model_str,
                bindings,
            });
        } else {
            let reason_str = format_unknown_reason(details.unknown_reason);
            // Same third-category split as `solve::solver_unknown_outcome`: if
            // ay caught its OWN invalid model, say so instead of letting the
            // reason-code mapping call it a theory incompleteness. Verdict
            // routing is unchanged (both are `is_incompleteness()`).
            let gate = model_gate_rejection(&details);
            let gate_suffix = gate
                .as_ref()
                .map(render_model_gate_rejection)
                .unwrap_or_default();
            let reason = format!(
                "Solver returned unknown ({}) for overflow check '{}' in '{}'{}",
                reason_str, check_name, assertion.name, gate_suffix
            );
            // Guarded relabel, never an unconditional override — see
            // `solve::gate_relabelled_category` for why a resource unknown must
            // keep its own category even when the gate fired.
            let category = gate_relabelled_category(
                classify_unknown_reason(details.unknown_reason, &reason),
                gate.is_some(),
            );
            return Ok(AssertionOutcome::unknown(reason.clone(), Some(category)));
        }
    }
    Ok(AssertionOutcome::Verified)
}
