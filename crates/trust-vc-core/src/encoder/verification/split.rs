//! Assertion splitting for localized error diagnostics.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! When a compound assertion fails (Counterexample), this module decomposes it
//! into independently-checkable sub-assertions and re-verifies each one to
//! pinpoint which conjunct(s) actually fail. Zero overhead on passing assertions.
//!
//! Part of #2485.

use std::collections::HashSet;

use super::assertion::verify_single_assertion_typed;
use super::outcome::AssertionOutcome;
use super::unknown_category::UnknownCategory;
use super::VerificationSlices;
use crate::error::TrustVcResult;
use crate::ir_expr::{LogicOp, QuantifierKind, TrustVcExpr};
use crate::prepared_context::PreparedObligation;

/// A sub-assertion produced by splitting a compound assertion expression.
pub(in crate::encoder) struct SubAssertion {
    /// Human-readable label: "conjunct 1 of 3", "consequent of implication", etc.
    pub label: String,
    /// The sub-expression to verify independently.
    pub expr: TrustVcExpr,
}

/// Decompose a compound assertion expression into independently-checkable
/// sub-assertions for localized error reporting.
///
/// Returns `None` if the expression is atomic (no useful split).
/// Returns `Some(sub_assertions)` with named sub-parts when splitting helps.
/// One level deep only — no recursive re-splitting of sub-conjuncts.
pub(in crate::encoder) fn split_assertion(expr: &TrustVcExpr) -> Option<Vec<SubAssertion>> {
    match expr {
        // Rule 1: Conjunction — flatten via collect_conjuncts
        TrustVcExpr::Logic {
            op: LogicOp::And, ..
        } => {
            let conjuncts = expr.collect_conjuncts();
            if conjuncts.len() < 2 {
                return None;
            }
            let n = conjuncts.len();
            Some(
                conjuncts
                    .into_iter()
                    .enumerate()
                    .map(|(i, c)| SubAssertion {
                        label: format!("conjunct {} of {}", i + 1, n),
                        expr: c.clone(),
                    })
                    .collect(),
            )
        }

        // Rule 2: Implication with compound consequent — split P ==> (A && B)
        // into [P ==> A, P ==> B]
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            let conjuncts = conclusion.collect_conjuncts();
            if conjuncts.len() < 2 {
                return None;
            }
            let n = conjuncts.len();
            Some(
                conjuncts
                    .into_iter()
                    .enumerate()
                    .map(|(i, c)| SubAssertion {
                        label: format!("implication consequent {} of {}", i + 1, n),
                        expr: TrustVcExpr::Implies {
                            premise: premise.clone(),
                            conclusion: Box::new(c.clone()),
                        },
                    })
                    .collect(),
            )
        }

        // Rule 3: If-then-else — split into then-case and else-case
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => Some(vec![
            SubAssertion {
                label: "then branch".to_string(),
                expr: TrustVcExpr::Implies {
                    premise: cond.clone(),
                    conclusion: then_branch.clone(),
                },
            },
            SubAssertion {
                label: "else branch".to_string(),
                expr: TrustVcExpr::Implies {
                    premise: Box::new(TrustVcExpr::Not(cond.clone())),
                    conclusion: else_branch.clone(),
                },
            },
        ]),

        // Rule 4: Forall with compound body — split forall |x| (A && B)
        // into [forall |x| A, forall |x| B]
        TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars,
            body,
            triggers,
            trigger_inference_mode,
        } => {
            let conjuncts = body.collect_conjuncts();
            if conjuncts.len() < 2 {
                return None;
            }
            let n = conjuncts.len();
            Some(
                conjuncts
                    .into_iter()
                    .enumerate()
                    .map(|(i, c)| SubAssertion {
                        label: format!("forall conjunct {} of {}", i + 1, n),
                        expr: TrustVcExpr::Quantifier {
                            kind: QuantifierKind::Forall,
                            bound_vars: bound_vars.clone(),
                            body: Box::new(c.clone()),
                            triggers: triggers.clone(),
                            trigger_inference_mode: *trigger_inference_mode,
                        },
                    })
                    .collect(),
            )
        }

        _ => None,
    }
}

/// Attempt to localize a failing assertion by splitting it into sub-assertions
/// and re-verifying each independently. Returns an enhanced `VerifyResult` with
/// per-conjunct pass/fail status, or `None` if the assertion can't be split.
///
/// Only called on the Counterexample path — zero overhead for passing assertions.
pub(super) fn try_localize_failure(
    slices: &VerificationSlices<'_>,
    assertion: &PreparedObligation,
    post_loop_modified_vars: Option<&HashSet<String>>,
    original_model: &Option<String>,
) -> Option<crate::encoder::types::VerifyResult> {
    let sub_assertions = split_assertion(&assertion.expr)?;

    let mut lines = vec![format!(
        "Assertion '{}' failed ({} sub-assertions):",
        assertion.name,
        sub_assertions.len()
    )];

    let mut first_fail_model: Option<String> = None;

    for sub in &sub_assertions {
        let sub_obligation = sub_obligation(assertion, &sub.label, sub.expr.clone());

        match verify_single_assertion_typed(slices, &sub_obligation, post_loop_modified_vars) {
            Ok(AssertionOutcome::Verified) => {
                lines.push(format!("  [PASS] {}", sub.label));
            }
            Ok(AssertionOutcome::Counterexample { model, .. }) => {
                lines.push(format!("  [FAIL] {}", sub.label));
                if first_fail_model.is_none() {
                    first_fail_model = model;
                }
            }
            Ok(AssertionOutcome::Unknown { reason, .. }) => {
                lines.push(format!("  [UNKNOWN] {}: {}", sub.label, reason));
            }
            Ok(AssertionOutcome::Error { message }) => {
                lines.push(format!("  [ERROR] {}: {}", sub.label, message));
            }
            Err(err) => {
                lines.push(format!("  [ERROR] {}: {}", sub.label, err));
            }
        }
    }

    // Append the model from the first failing sub-assertion (or fall back to original).
    if let Some(ref model) = first_fail_model.as_ref().or(original_model.as_ref()) {
        lines.push(format!("Counterexample: {model}"));
    }

    let enhanced_model = lines.join("\n");

    Some(crate::encoder::types::VerifyResult::Counterexample {
        obligation_name: assertion.display_name().to_string(),
        location: assertion.location.clone(),
        model: Some(enhanced_model),
        bindings: Vec::new(),
    })
}

/// Build a sub-obligation that carries `expr`/`label` while inheriting every
/// contextual field (solver mode, triggers, broadcast group, …) of the parent
/// `assertion`, so the sub-assertion is verified under an identical context.
fn sub_obligation(
    assertion: &PreparedObligation,
    label: &str,
    expr: TrustVcExpr,
) -> PreparedObligation {
    PreparedObligation {
        name: format!("{} [{}]", assertion.name, label),
        expr,
        kind: assertion.kind,
        location: assertion.location.clone(),
        condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
        bound_vars: assertion.bound_vars.clone(),
        trigger_patterns: assertion.trigger_patterns.clone(),
        prepared_triggers: assertion.prepared_triggers.clone(),
        solver_mode: assertion.solver_mode,
        is_opaque: assertion.is_opaque,
        is_inline: assertion.is_inline,
        broadcast_group: assertion.broadcast_group.clone(),
        condition: assertion.condition.clone(),
        invariant_namespace: assertion.invariant_namespace,
        trigger_inference_mode: assertion.trigger_inference_mode,
        broadcast_guard: assertion.broadcast_guard.clone(),
        raw_broadcast_guard_count: assertion.raw_broadcast_guard_count,
        step_meta: assertion.step_meta.clone(),
    }
}

/// True iff `expr` is a TRIGGERLESS universal whose body is a conjunction of
/// `>= 2` conjuncts that contains a nested quantifier — the exact shape for which
/// the single-solve refutation is UNSOUND.
///
/// Refuting `∀i. (C₁ ∧ C₂)` builds `∃i. (¬C₁ ∨ ¬C₂)` over one free Skolem
/// witness `i`. When one conjunct refutes to a real nested quantifier (e.g.
/// refuting an inner `exists j. j > i` yields `forall j. j ≤ i`) and another
/// refutes to a *satisfiable* ground predicate over the same witness (e.g.
/// `i ≤ 1000`), ay decides the mixed (quantified-disjunct ∨ ground-disjunct)
/// goal UNSOUNDLY — returning spurious UNSAT and swallowing the ground
/// counterexample, so a genuinely-false universal is reported `Verified`
/// (round-4 quantifiers finding). The conjunct-split path
/// (`try_verify_quantified_conjunction_split`) discharges this shape soundly;
/// `can_use_shared_bv_fast_path` consults this predicate to route such an
/// assertion to the per-assertion fallback (which runs the conjunct split)
/// instead of the shared-BV fast path.
pub(in crate::encoder) fn is_quantified_conjunction_forall(expr: &TrustVcExpr) -> bool {
    let TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        body,
        triggers,
        ..
    } = expr
    else {
        return false;
    };
    let triggerless = triggers.as_ref().is_none_or(|groups| groups.is_empty());
    triggerless && body.collect_conjuncts().len() >= 2 && body.contains_quantifier()
}

/// Soundly discharge a triggerless `forall|x| (C₁ ∧ C₂ ∧ …)` whose body
/// conjunction contains a nested quantifier by verifying each conjunct's
/// universal `forall|x| Cₖ` as a SEPARATE solver query, then combining:
///
/// * any conjunct ⇒ Counterexample  →  the universal is genuinely false
///   (Counterexample, with per-conjunct localization);
/// * all conjuncts ⇒ Verified        →  the universal genuinely holds (Verified);
/// * otherwise (some Unknown/Error, no Counterexample) → fail closed (Unknown).
///
/// This is the exact quantifier-distribution law
/// `∀x.(A ∧ B) ⟺ (∀x.A) ∧ (∀x.B)`, so it is sound and — for a conjunction whose
/// conjuncts are logically independent — complete. Crucially, each separate
/// query is EITHER a pure quantifier refutation OR a pure ground refutation, so
/// it never builds the mixed (quantified-disjunct ∨ ground-disjunct) goal that
/// ay decides unsoundly in the single-solve path.
///
/// Returns `Ok(None)` when the assertion is not of the targeted shape (caller
/// proceeds with the ordinary single-solve path — zero behavior change for every
/// other assertion).
pub(super) fn try_verify_quantified_conjunction_split(
    slices: &VerificationSlices<'_>,
    assertion: &PreparedObligation,
    post_loop_modified_vars: Option<&HashSet<String>>,
) -> TrustVcResult<Option<AssertionOutcome>> {
    if !is_quantified_conjunction_forall(&assertion.expr) {
        return Ok(None);
    }
    let Some(sub_assertions) = split_assertion(&assertion.expr) else {
        return Ok(None);
    };

    let mut lines = vec![format!(
        "Assertion '{}' failed ({} sub-assertions):",
        assertion.name,
        sub_assertions.len()
    )];
    let mut first_fail_model: Option<String> = None;
    let mut saw_counterexample = false;
    let mut blocking_unknown: Option<AssertionOutcome> = None;
    let mut blocking_error: Option<String> = None;

    for sub in &sub_assertions {
        let sub_obligation = sub_obligation(assertion, &sub.label, sub.expr.clone());
        match verify_single_assertion_typed(slices, &sub_obligation, post_loop_modified_vars)? {
            AssertionOutcome::Verified => {
                lines.push(format!("  [PASS] {}", sub.label));
            }
            AssertionOutcome::Counterexample { model, .. } => {
                saw_counterexample = true;
                lines.push(format!("  [FAIL] {}", sub.label));
                if first_fail_model.is_none() {
                    first_fail_model = model;
                }
            }
            unknown @ AssertionOutcome::Unknown { .. } => {
                lines.push(format!("  [UNKNOWN] {}", sub.label));
                if blocking_unknown.is_none() {
                    blocking_unknown = Some(unknown);
                }
            }
            AssertionOutcome::Error { message } => {
                lines.push(format!("  [ERROR] {}: {}", sub.label, message));
                if blocking_error.is_none() {
                    blocking_error = Some(message);
                }
            }
        }
    }

    // A genuine counterexample for ANY conjunct refutes the whole universal —
    // decisive even when a sibling conjunct is Unknown.
    if saw_counterexample {
        if let Some(model) = first_fail_model.as_ref() {
            lines.push(format!("Counterexample: {model}"));
        }
        return Ok(Some(AssertionOutcome::Counterexample {
            obligation_name: assertion.display_name().to_string(),
            location: assertion.location.clone(),
            model: Some(lines.join("\n")),
            bindings: Vec::new(),
        }));
    }
    if let Some(message) = blocking_error {
        return Ok(Some(AssertionOutcome::Error { message }));
    }
    // Fail closed: a conjunct could not be discharged, so the conjunction cannot
    // be soundly reported Verified (the single-solve `Verified` for this shape is
    // exactly the unsound result this path replaces).
    if let Some(AssertionOutcome::Unknown {
        reason,
        category,
        detail,
    }) = blocking_unknown
    {
        return Ok(Some(AssertionOutcome::unknown_with_detail(
            format!(
                "triggerless quantified-conjunction conjunct could not be soundly \
                 discharged in isolation: {reason}"
            ),
            category.or(Some(UnknownCategory::Incompleteness)),
            detail,
        )));
    }

    Ok(Some(AssertionOutcome::Verified))
}
