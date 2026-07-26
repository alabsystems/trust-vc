//! Inductive-step verification logic for loop invariants.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod frame_condition;
mod havoc_all;

use super::outcome::AssertionOutcome;
use super::unknown_category::UnknownCategory;
use super::PRE_STATE_SUFFIX;
use crate::encoder::{
    diagnostics::{EncodingApproximation, EncodingDiagnostics},
    AYEncoder, BROADCAST_INSTANCE_CAP,
};
use crate::error::{TrustVcError, TrustVcResult};
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
use crate::vc::ObligationKind;

const BROADCAST_SETUP_CONTEXT: &str = "build inductive-step broadcast assumptions";

pub(super) fn wrap_setup_error(
    err: TrustVcError,
    context: &'static str,
    message: impl FnOnce(&str) -> String,
) -> TrustVcError {
    match err {
        TrustVcError::Encoding { detail, .. } => TrustVcError::Encoding {
            context,
            detail: message(&detail),
        },
        TrustVcError::Internal { detail, .. } => TrustVcError::Internal {
            context,
            detail: message(&detail),
        },
        other => other,
    }
}

fn demote_verified_inductive_result(
    outcome: AssertionOutcome,
    target: &str,
    diagnostics: &EncodingDiagnostics,
) -> AssertionOutcome {
    if matches!(outcome, AssertionOutcome::Verified) && diagnostics.has_demoting() {
        AssertionOutcome::Unknown {
            reason: diagnostics.demotion_reason(target),
            category: Some(UnknownCategory::EncodingDemotion),
            detail: None,
        }
    } else {
        outcome
    }
}

fn run_inductive_verification(
    ctx: &PreparedVerificationContext,
    invariant: &PreparedObligation,
    build_encoder: impl Fn() -> TrustVcResult<AYEncoder>,
) -> TrustVcResult<AssertionOutcome> {
    let mut run_diagnostics = EncodingDiagnostics::default();

    if ctx.check_overflow() {
        let mut overflow_encoder = match build_encoder() {
            Ok(enc) => enc,
            Err(err) => return super::assertion::convert_setup_error(err),
        };
        let overflow_outcome =
            super::overflow::check_overflow_predicates(&mut overflow_encoder, invariant, true)?;
        run_diagnostics.merge(&overflow_encoder.state.diagnostics);
        if !matches!(overflow_outcome, AssertionOutcome::Verified) {
            return Ok(overflow_outcome);
        }
    }

    let result = super::confirmation::verify_with_confirmation(
        build_encoder,
        invariant,
        ctx.has_collection_context,
        ctx.rlimit_ms,
    )?;
    Ok(demote_verified_inductive_result(
        result,
        &invariant.name,
        &run_diagnostics,
    ))
}

impl AYEncoder {
    /// Typed inductive step — operates directly on PreparedVerificationContext.
    /// Uses the invariant's `TrustVcExpr` directly and adds previously verified
    /// invariants as assumptions so inter-dependent invariants stay available.
    pub(in crate::encoder) fn verify_invariant_inductive_step_typed(
        ctx: &PreparedVerificationContext,
        invariant: &PreparedObligation,
        verified_invariants: &[&PreparedObligation],
    ) -> TrustVcResult<AssertionOutcome> {
        let modified_vars = ctx.loop_modified_vars.get(&invariant.name);
        let loop_guard = ctx.loop_guards.get(&invariant.name);

        if let Some(modified) = modified_vars {
            frame_condition::verify_inductive_step_frame_condition_typed(
                ctx,
                invariant,
                modified,
                loop_guard,
                verified_invariants,
            )
        } else {
            havoc_all::verify_inductive_step_havoc_all_typed(ctx, invariant, verified_invariants)
        }
    }

    /// Adds broadcast assumptions from a PreparedVerificationContext.
    /// Delegates to `add_typed_broadcast` so broadcast setup stays shared
    /// between main assertions and inductive steps. Fixes #2244.
    ///
    /// `goal` is the loop invariant/measure being proven; grouped broadcast
    /// axioms are gated FORWARD-ONLY against its body position (parity with
    /// `register_setup_broadcasts`), so a file-path `broadcast_use!` after the
    /// loop never activates a group inside the loop's inductive step.
    fn add_broadcasts_for_inductive_step(
        &mut self,
        ctx: &PreparedVerificationContext,
        goal: Option<&PreparedObligation>,
    ) -> TrustVcResult<()> {
        let is_recursive_fn = ctx
            .function_context
            .as_ref()
            .is_some_and(|fc| fc.is_recursive);
        let all_var_terms: Vec<_> = self
            .variables
            .iter()
            .filter(|(name, _)| !name.contains(PRE_STATE_SUFFIX))
            .map(|(_, &term)| term)
            .collect();

        // Use pre-computed revealed_fns from PreparedVerificationContext.
        // Part of #1901, optimized in #1786.
        let revealed_fns = &ctx.revealed_fns;

        // FORWARD-ONLY snapshot of the file-path broadcast groups active at the
        // inductive-step goal's body position (parity with
        // `register_setup_broadcasts`). Unioned with the session-path
        // positionless set below.
        let active_groups =
            super::setup::setup_broadcasts::active_broadcast_groups_before(ctx, goal);

        // Stage candidate source expressions for the interpreted-op
        // dead-trigger broadcast ground replay (parity with
        // `setup_broadcasts.rs`; see `broadcast.rs`).
        if ctx.obligations.iter().any(|obligation| {
            obligation.kind == ObligationKind::BroadcastAssume
                && crate::encoder::verification::broadcast::interpreted_dead_trigger_patterns(
                    obligation,
                )
                .is_some()
        }) {
            self.state.broadcast_ground_replay_sources = ctx
                .obligations
                .iter()
                .filter(|obligation| obligation.kind != ObligationKind::BroadcastAssume)
                .map(|obligation| obligation.expr.clone())
                .collect();
        }

        for obligation in &ctx.obligations {
            if obligation.kind != ObligationKind::BroadcastAssume {
                continue;
            }
            // Position-aware broadcast_use_groups filter: skip grouped
            // broadcasts unless the group is activated at the goal's body
            // position — by a body-ordered file-path `broadcast_use!` marker
            // preceding the goal (`active_groups`) or by the session-path
            // positionless set (`ctx.broadcast_use_groups`). Parity with
            // `register_setup_broadcasts`. Part of #2555.
            if let Some(ref group) = obligation.broadcast_group {
                if !active_groups.contains(group.as_str())
                    && !ctx.broadcast_use_groups.contains(group)
                {
                    continue;
                }
            }
            // Inline body axiom skip: inline spec functions use call-site
            // substitution (via inline_bodies populated by bootstrap_prepared_encoder).
            // Use successful extraction, not the obligation name suffix, so
            // proc-macro body axioms with module-path suffixes still skip the
            // redundant broadcast path. If extraction failed, fall through to
            // broadcast axiom path. Parity with setup_from_prepared. Part of #2555, #2568.
            if super::body_support::inline_body_axiom_extracted(obligation) {
                continue;
            }
            // Opaque/hidden filter: skip opaque (`#[trust_vc::opaque]`) and
            // hidden (`hide!`) body axioms unless revealed (reveal wins over
            // hide). Parity with `setup_broadcasts.rs`. Part of #1901.
            // Axiom names: "__body_axiom_{fn_name}" (encoder tests) or
            // "__body_axiom_{fn_name}_{module_path}" (proc-macro path, spec_expand.rs).
            // Matching (name suffix, trigger head, or qualified trigger-head leaf
            // for cross-crate dependency axioms) lives in
            // `body_axiom_fn_named_in`. Part of #2429, #2778.
            if super::body_support::is_body_axiom(obligation)
                && (obligation.is_opaque
                    || super::body_support::body_axiom_fn_named_in(obligation, &ctx.hidden_fns))
                && !super::body_support::opaque_body_axiom_revealed(obligation, revealed_fns)
            {
                continue;
            }
            if is_recursive_fn && super::body_support::is_body_axiom(obligation) {
                // Direct defining axiom for recursive body unfolding.
                // Uses original function name with E-matching trigger. Part of #2155, #2187.
                if let Some(ref func_ctx) = ctx.function_context {
                    crate::encoder::fuel::encode_fuel_axioms(
                        self,
                        func_ctx,
                        obligation,
                        &all_var_terms,
                    )
                    .map_err(|err| {
                        wrap_setup_error(err, BROADCAST_SETUP_CONTEXT, |detail| detail.to_string())
                    })?;
                    continue;
                }
            }
            self.state.broadcast_count += 1;
            if self.state.broadcast_count > BROADCAST_INSTANCE_CAP {
                self.state
                    .diagnostics
                    .record(EncodingApproximation::BroadcastCapHit);
                // Build `guard ==> body` for guarded broadcasts (#2727).
                // The normal path uses `add_typed_broadcast` which handles this,
                // but the cap fallback must construct the implication manually.
                let fallback_expr = if let Some(ref guard) = obligation.broadcast_guard {
                    crate::ir::TrustVcExpr::Implies {
                        premise: Box::new(guard.clone()),
                        conclusion: Box::new(obligation.expr.clone()),
                    }
                } else {
                    obligation.expr.clone()
                };
                self.add_typed_assumption(&obligation.name, &fallback_expr, None)
                    .map_err(|err| {
                        wrap_setup_error(err, BROADCAST_SETUP_CONTEXT, |detail| detail.to_string())
                    })?;
                continue;
            }
            self.add_typed_broadcast(obligation, &all_var_terms)
                .map_err(|err| {
                    wrap_setup_error(err, BROADCAST_SETUP_CONTEXT, |detail| detail.to_string())
                })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::TrustVcType;
    use crate::mode::FunctionMode;
    use crate::prepared_context::prepare_context;
    use crate::vc::{FunctionContext, ProofObligation, VerificationContext};

    fn setup_body_axiom_context(
        is_inline: bool,
        broadcast_group: Option<&str>,
        use_group: bool,
    ) -> VerificationContext {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
        ctx.set_function_context(FunctionContext {
            name: "double".to_string(),
            params: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
            return_type: TrustVcType::Int { width: 32 },
            is_recursive: false,
            mode: FunctionMode::Spec,
            trait_bounds: vec![],
        });

        let mut body_axiom =
            ProofObligation::broadcast_assume("__body_axiom_double", "double(x) == x + x")
                .with_bound_vars(vec!["x".to_string()])
                .with_trigger_patterns(vec![vec!["double(x)".to_string()]])
                .with_inline(is_inline);
        if let Some(group) = broadcast_group {
            body_axiom = body_axiom.with_broadcast_group(group);
            if use_group {
                ctx.add_broadcast_use_group(group);
            }
        }
        ctx.obligations.push(body_axiom);
        ctx
    }

    fn setup_body_axiom_context_with_name(
        axiom_name: &str,
        is_inline: bool,
        broadcast_group: Option<&str>,
        use_group: bool,
    ) -> VerificationContext {
        let mut ctx = setup_body_axiom_context(false, broadcast_group, use_group);
        ctx.obligations.clear();

        let mut body_axiom = ProofObligation::broadcast_assume(axiom_name, "double(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["double(x)".to_string()]])
            .with_inline(is_inline);
        if let Some(group) = broadcast_group {
            body_axiom = body_axiom.with_broadcast_group(group);
        }
        ctx.obligations.push(body_axiom);
        ctx
    }

    fn bootstrap_inductive_encoder(
        ctx: &VerificationContext,
    ) -> (PreparedVerificationContext, AYEncoder) {
        let prepared = prepare_context(ctx).expect("body axiom test context should prepare");
        let broadcast_assumptions: Vec<_> = prepared
            .obligations
            .iter()
            .filter(|obligation| obligation.kind == ObligationKind::BroadcastAssume)
            .collect();
        let mut encoder = AYEncoder::new();
        super::super::setup::bootstrap_prepared_encoder(
            &mut encoder,
            &prepared,
            super::super::setup::BootstrapPreparedConfig {
                active_broadcasts: &broadcast_assumptions,
                active_assumptions: &[],
                verified_invariants: &[],
                verified_assert_by: &[],
                scoped_assumptions: &[],
                use_int_for_measures: false,
                extra_variables: &[],
                assertion_focus: None,
                enable_current_state_variable_slice: false,
                inline_overrides: &[],
                allow_finite_len_pins: false,
            },
        )
        .expect("inductive-step bootstrap should succeed");
        (prepared, encoder)
    }

    #[test]
    fn test_inductive_step_skips_grouped_broadcasts_outside_broadcast_use_scope() {
        let ctx = setup_body_axiom_context(false, Some("helpers"), false);
        let (prepared, mut encoder) = bootstrap_inductive_encoder(&ctx);

        encoder
            .add_broadcasts_for_inductive_step(&prepared, None)
            .expect("inductive-step broadcast setup should succeed");

        assert_eq!(
            encoder.state.broadcast_count, 0,
            "grouped broadcasts must stay out of the inductive step unless broadcast_use! activates the group"
        );
    }

    #[test]
    fn test_inductive_step_adds_grouped_broadcasts_when_group_is_in_scope() {
        let ctx = setup_body_axiom_context(false, Some("helpers"), true);
        let (prepared, mut encoder) = bootstrap_inductive_encoder(&ctx);

        encoder
            .add_broadcasts_for_inductive_step(&prepared, None)
            .expect("inductive-step broadcast setup should succeed");

        assert_eq!(
            encoder.state.broadcast_count, 1,
            "grouped broadcasts should reach the inductive step once broadcast_use! activates the group"
        );
    }

    #[test]
    fn test_inductive_step_skips_inline_body_axiom_after_inline_extraction() {
        let ctx = setup_body_axiom_context(true, None, false);
        let (prepared, mut encoder) = bootstrap_inductive_encoder(&ctx);

        assert!(
            encoder.state.inline_bodies.contains_key("double"),
            "bootstrap should extract inline body axioms for call-site substitution before the inductive step"
        );

        encoder
            .add_broadcasts_for_inductive_step(&prepared, None)
            .expect("inductive-step broadcast setup should succeed");

        assert_eq!(
            encoder.state.broadcast_count, 0,
            "inline body axioms must not be re-emitted into the inductive step after extraction"
        );
    }

    #[test]
    fn test_inductive_step_skips_module_suffixed_inline_body_axiom_after_extraction() {
        let ctx = setup_body_axiom_context_with_name(
            "__body_axiom_double_inline_spec",
            true,
            None,
            false,
        );
        let (prepared, mut encoder) = bootstrap_inductive_encoder(&ctx);

        assert!(
            encoder.state.inline_bodies.contains_key("double"),
            "bootstrap should extract inline bodies by function call name, not by obligation suffix"
        );

        encoder
            .add_broadcasts_for_inductive_step(&prepared, None)
            .expect("inductive-step broadcast setup should succeed");

        assert_eq!(
            encoder.state.broadcast_count, 0,
            "module-suffixed inline body axioms must still skip the inductive-step broadcast path after extraction"
        );
    }
}
