//! Broadcast registration lane extracted from setup.rs.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use ay_dpll::api::Term;

use crate::encoder::diagnostics::EncodingApproximation;
use crate::encoder::verification::body_support;
use crate::encoder::verification::pruning::PrunePlan;
use crate::encoder::{AYEncoder, BROADCAST_INSTANCE_CAP};
use crate::error::TrustVcResult;
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
use crate::vc::ObligationKind;

/// The broadcast groups activated by `broadcast_use!` markers whose body
/// position lexically PRECEDES the current goal (`goal`).
///
/// SOUNDNESS-CRITICAL (file-path `broadcast_use!` reinstatement): the file path
/// lowers each `broadcast_use!(g)` to a body-ordered [`ObligationKind::BroadcastUse`]
/// marker in `ctx.obligations`. A grouped broadcast axiom for `g` is admissible
/// for a proof obligation only if that obligation sits at or after the marker's
/// program point — FORWARD-ONLY activation. Folding activation into a
/// function-global set (the pre-quarantine behavior) applied a group activated
/// ANYWHERE (even the last statement) to EVERY assertion, including ones
/// textually before the use site — a retroactive false-verify. This snapshot is
/// computed AT the goal's position instead.
///
/// The goal's body position is located by pointer identity (the real assertion
/// path passes a borrow of `ctx.obligations`), falling back to name — a split
/// sub-obligation clones the parent's name as `"{name} [label]"`, so the base
/// name recovers the parent's position (all conjuncts of one assert share the
/// parent's activation snapshot). A goal that cannot be located returns the
/// empty set — no file-path grouped broadcast activates — which fails closed.
pub(crate) fn active_broadcast_groups_before<'a>(
    ctx: &'a PreparedVerificationContext,
    goal: Option<&PreparedObligation>,
) -> HashSet<&'a str> {
    let mut active: HashSet<&str> = HashSet::new();
    let Some(goal) = goal else {
        return active;
    };
    let goal_pos = ctx
        .obligations
        .iter()
        .position(|obligation| std::ptr::eq(obligation, goal))
        .or_else(|| {
            // Recover the ORIGINATING assertion's body position for a synthesized
            // goal that is not itself in the stream. A negated broadcast-vacuity
            // probe is named `__vacuity_probe_{name}` and re-verifies the goal in
            // the IDENTICAL context, so it MUST see the same active groups (else
            // the vacuity probe checks ¬G without the grouped axiom and cannot
            // catch a contradictory lemma). A split sub-obligation clones the
            // parent name as `"{name} [label]"`. Strip both to reach the base.
            let base = goal
                .name
                .strip_prefix("__vacuity_probe_")
                .unwrap_or(goal.name.as_str());
            let base = base.split(" [").next().unwrap_or(base);
            ctx.obligations
                .iter()
                .position(|obligation| obligation.name == goal.name || obligation.name == base)
        });
    let Some(goal_pos) = goal_pos else {
        return active;
    };
    for obligation in &ctx.obligations[..goal_pos] {
        if obligation.kind == ObligationKind::BroadcastUse {
            if let Some(group) = obligation.broadcast_group.as_deref() {
                active.insert(group);
            }
        }
    }
    active
}

pub(super) fn register_setup_broadcasts(
    encoder: &mut AYEncoder,
    ctx: &PreparedVerificationContext,
    broadcast_assumptions: &[&PreparedObligation],
    prune_plan: &PrunePlan,
    var_terms: &[Term],
    assertion_focus: Option<&PreparedObligation>,
) -> TrustVcResult<()> {
    // FORWARD-ONLY snapshot of the file-path broadcast groups active at the
    // current goal's body position. Session-path activation stays in
    // `ctx.broadcast_use_groups` (positionless, unchanged); the two are unioned
    // in the gate below so neither front end regresses.
    let active_groups = active_broadcast_groups_before(ctx, assertion_focus);
    let is_recursive_fn = ctx
        .function_context
        .as_ref()
        .is_some_and(|fc| fc.is_recursive);
    let revealed_fns = &ctx.revealed_fns;
    let hidden_fns = &ctx.hidden_fns;

    // Interpreted-op dead-trigger broadcasts (e.g. trigger `x * x`) are
    // ground-replayed by matching their trigger patterns against the
    // goal/assumption expressions at the IR level (ay's E-matcher cannot index
    // interpreted heads — see `broadcast.rs`). Stage the candidate source
    // expressions only when such a broadcast is present, so the common
    // (uninterpreted-trigger) path pays nothing.
    if broadcast_assumptions.iter().any(|broadcast| {
        crate::encoder::verification::broadcast::interpreted_dead_trigger_patterns(broadcast)
            .is_some()
    }) {
        encoder.state.broadcast_ground_replay_sources = ctx
            .obligations
            .iter()
            .filter(|obligation| obligation.kind != crate::vc::ObligationKind::BroadcastAssume)
            .map(|obligation| obligation.expr.clone())
            .collect();
    }

    for broadcast in broadcast_assumptions {
        if !prune_plan.is_broadcast_reachable(broadcast) {
            continue;
        }
        if let Some(ref group) = broadcast.broadcast_group {
            // Position-aware gate: a grouped broadcast axiom is admissible only
            // if its group is activated at the goal's body position — either by
            // a body-ordered file-path `broadcast_use!` marker that PRECEDES the
            // goal (`active_groups`) or by the session-path positionless set
            // (`ctx.broadcast_use_groups`). A group activated only AFTER the goal
            // (retroactive) is excluded — the core soundness fix.
            if !active_groups.contains(group.as_str()) && !ctx.broadcast_use_groups.contains(group)
            {
                continue;
            }
        }
        // Opaque/hidden filter: skip opaque (`#[trust_vc::opaque]`) and hidden
        // (`hide!`) body axioms unless revealed — reveal wins over hide, which
        // nets the upstream Verus verdicts for basic.rs `test_spec_fn`'s
        // `hide(f2) … reveal(f2)` sequence under trust-vc's query-granular
        // reveal model. Part of #1901.
        // Axiom names: "__body_axiom_{fn_name}" (encoder tests) or
        // "__body_axiom_{fn_name}_{module_path}" (proc-macro path, spec_expand.rs).
        // Matching (name suffix, trigger head, or qualified trigger-head leaf for
        // cross-crate dependency axioms) lives in `body_axiom_fn_named_in`.
        // Part of #2429, #2778.
        if body_support::is_body_axiom(broadcast)
            && (broadcast.is_opaque || body_support::body_axiom_fn_named_in(broadcast, hidden_fns))
            && !body_support::opaque_body_axiom_revealed(broadcast, revealed_fns)
        {
            continue;
        }
        // Inline spec functions: extract the body for call-site substitution
        // instead of ALSO emitting the UF's quantified defining axiom. This
        // covers both source-declared inline functions and attempt-local
        // demand-inline overrides already installed in `inline_bodies`.
        //
        // Keeping an overridden axiom live defeats the retry's purpose: the
        // goal is ground after exact substitution, but the redundant forall can
        // still make AY's candidate-model certification fail closed to Unknown.
        // Use successful body extraction, not the obligation-name suffix,
        // because proc-macro axioms append module-path suffixes. A malformed
        // body falls through to the broadcast path, never silently leaving the
        // function uninterpreted. Part of #2488, #2568, #2655.
        let substituted_at_calls =
            body_support::extracted_body_axiom(broadcast).is_some_and(|body| {
                encoder
                    .state
                    .inline_bodies
                    .contains_key(&body.function_name)
            });
        if body_support::inline_body_axiom_extracted(broadcast) || substituted_at_calls {
            continue;
        }
        if is_recursive_fn && body_support::is_body_axiom(broadcast) {
            // Direct defining axiom for recursive body unfolding.
            // Uses original function name with E-matching trigger. Part of #2155, #2187.
            if let Some(ref func_ctx) = ctx.function_context {
                crate::encoder::fuel::encode_fuel_axioms(encoder, func_ctx, broadcast, var_terms)
                    .map_err(|e| {
                    super::setup_encoding_error(format!(
                        "Fuel encoding failed for '{}': {}",
                        broadcast.name, e,
                    ))
                })?;
                continue;
            }
        }
        encoder.state.broadcast_count += 1;
        if encoder.state.broadcast_count > BROADCAST_INSTANCE_CAP {
            encoder
                .state
                .diagnostics
                .record(EncodingApproximation::BroadcastCapHit);
            // Build `guard ==> body` for guarded broadcasts (#2727).
            // The normal path uses `add_typed_broadcast` which handles this,
            // but the cap fallback must construct the implication manually.
            let fallback_expr = if let Some(ref guard) = broadcast.broadcast_guard {
                crate::ir::TrustVcExpr::Implies {
                    premise: Box::new(guard.clone()),
                    conclusion: Box::new(broadcast.expr.clone()),
                }
            } else {
                broadcast.expr.clone()
            };
            encoder.add_typed_assumption(&broadcast.name, &fallback_expr, None)?;
        } else {
            encoder.add_typed_broadcast(broadcast, var_terms)?;
        }
    }

    Ok(())
}
