//! Frame-condition inductive-step verification.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use super::AssertionOutcome;
use crate::encoder::{diagnostics::EncodingApproximation, AYEncoder};
use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::{CompareOp, TrustVcExpr, TrustVcType};
use crate::ir_lowering::{lower_syn_expr, TypeEnv};
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
use crate::vc::ObligationKind;

const FRAME_SETUP_CONTEXT: &str = "build frame-condition inductive-step encoder";

/// Collects every variable NAME a `TrustVcExpr` can reference, including the
/// receiver/place metadata names that `replace_vars_with_pre_typed_with_targets`
/// rewrites. Quantifier-bound names are over-approximated as referenced — that
/// only makes the unmodified-precondition gate MORE conservative (it would skip a
/// precondition, never wrongly assume one), preserving soundness.
fn collect_referenced_var_names(expr: &TrustVcExpr) -> HashSet<String> {
    use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};

    #[derive(Default)]
    struct Collector {
        names: HashSet<String>,
    }
    impl TrustVcExprVisitor for Collector {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            match expr {
                TrustVcExpr::Var { name, .. } => {
                    self.names.insert(name.clone());
                }
                TrustVcExpr::CollectionOp {
                    receiver_name: Some(n),
                    ..
                }
                | TrustVcExpr::Index {
                    receiver_name: Some(n),
                    ..
                } => {
                    self.names.insert(n.clone());
                }
                TrustVcExpr::ReadPlace { place, .. } => {
                    self.names.insert(place.root_name.clone());
                }
                TrustVcExpr::PlaceDisjoint { left, right } => {
                    self.names.insert(left.root_name.clone());
                    self.names.insert(right.root_name.clone());
                }
                _ => {}
            }
            walk_expr(self, expr);
        }
    }

    let mut collector = Collector::default();
    collector.visit_expr(expr);
    collector.names
}

/// Mode 2 typed: Frame condition inductive step.
/// Uses pre/post state variables plus frame conditions for unmodified
/// variables while keeping earlier invariants available in pre-state form.
pub(super) fn verify_inductive_step_frame_condition_typed(
    ctx: &PreparedVerificationContext,
    invariant: &PreparedObligation,
    modified_vars: &[String],
    loop_guard: Option<&String>,
    verified_invariants: &[&PreparedObligation],
) -> TrustVcResult<AssertionOutcome> {
    let pre_state_targets = super::super::rewrite::collect_pre_state_target_names(&ctx.variables);

    let transitions = ctx.loop_body_transitions.get(&invariant.name);
    let has_transitions = transitions.is_some_and(|t| !t.is_empty());

    // Build the pre-state type environment once if we need to lower the loop
    // guard or any body transition expression. Pre-lowering avoids repeated
    // syn::parse_str + lower_syn_expr inside each setup_frame_condition_encoder
    // call (the setup is called 2-4× per invariant). Part of #1786 / M4.
    let env = (loop_guard.is_some() || has_transitions).then(|| build_pre_state_env(ctx));

    let pre_guard_expr = match (loop_guard, env.as_ref()) {
        (Some(guard_condition), Some(env)) => {
            let guard_expr = lower_string_condition(guard_condition, env)?;
            Some(
                super::super::rewrite::replace_vars_with_pre_typed_with_targets(
                    &guard_expr,
                    &pre_state_targets,
                ),
            )
        }
        _ => None,
    };

    // Pre-lower each modified var's single-iteration transition RHS and rename
    // its variable references to the pre-state. The result `(var, ty, rhs_pre)`
    // becomes the assumption `var == rhs_pre` in the inductive step, binding the
    // havoc'd current-state `var` to `f(pre-state)`. A transition that fails to
    // lower is skipped (the var stays havoc'd — sound, incomplete). Part of M4.
    let pre_transition_exprs: Vec<(String, TrustVcType, TrustVcExpr)> =
        match (transitions, env.as_ref()) {
            (Some(transitions), Some(env)) => transitions
                .iter()
                .filter_map(|(var, rhs)| {
                    let ty = ctx.variables.iter().find(|v| &v.name == var)?.ty.clone();
                    let rhs_expr = lower_string_condition(rhs, env).ok()?;
                    let rhs_pre = super::super::rewrite::replace_vars_with_pre_typed_with_targets(
                        &rhs_expr,
                        &pre_state_targets,
                    );
                    Some((var.clone(), ty, rhs_pre))
                })
                .collect(),
            _ => Vec::new(),
        };

    super::run_inductive_verification(ctx, invariant, || {
        setup_frame_condition_encoder(
            ctx,
            invariant,
            modified_vars,
            pre_guard_expr.as_ref(),
            &pre_transition_exprs,
            &pre_state_targets,
            verified_invariants,
        )
    })
}

/// Builds a `TypeEnv` holding every context variable in both its current-state
/// and pre-state (`__trust_vc_pre`) forms, plus the function-context return type
/// when present and non-opaque. Shared by the guard and body-transition
/// pre-lowering. Part of M4.
fn build_pre_state_env(ctx: &PreparedVerificationContext) -> TypeEnv {
    let mut env = TypeEnv::new();
    for var in &ctx.variables {
        env.insert(var.name.clone(), var.ty.clone());
        env.insert(
            format!("{}{}", var.name, super::super::PRE_STATE_SUFFIX),
            var.ty.clone(),
        );
    }
    if let Some(ref func_ctx) = ctx.function_context {
        if !func_ctx.return_type.contains_opaque() {
            env.insert_fn(func_ctx.name.clone(), func_ctx.return_type.clone());
        }
    }
    env
}

/// Build a configured encoder for frame-condition inductive step.
///
/// Extracted so it can be called multiple times: once for overflow checking
/// (discarded), once for the main assertion, and optionally for
/// confirmation/retry. Part of #2246.
///
/// `pre_guard_expr` is the pre-lowered and pre-state-renamed loop guard
/// TrustVcExpr, computed once by the caller to avoid repeated syn::parse_str
/// + lower_syn_expr. Part of #1786.
fn setup_frame_condition_encoder(
    ctx: &PreparedVerificationContext,
    invariant: &PreparedObligation,
    modified_vars: &[String],
    pre_guard_expr: Option<&TrustVcExpr>,
    pre_transition_exprs: &[(String, TrustVcType, TrustVcExpr)],
    pre_state_targets: &HashSet<&str>,
    verified_invariants: &[&PreparedObligation],
) -> TrustVcResult<AYEncoder> {
    let timeout_ms = ctx.rlimit_ms.unwrap_or(30_000);
    let mut encoder = AYEncoder::new().with_limits(timeout_ms, 512);
    let modified_set: HashSet<&str> = modified_vars.iter().map(|s| s.as_str()).collect();
    let broadcast_assumptions: Vec<_> = ctx
        .obligations
        .iter()
        .filter(|obligation| matches!(obligation.kind, crate::vc::ObligationKind::BroadcastAssume))
        .collect();

    // Record opaque return type diagnostic if applicable. #2314.
    if let Some(ref func_ctx) = ctx.function_context {
        if func_ctx.return_type.contains_opaque() {
            encoder
                .state
                .diagnostics
                .record(EncodingApproximation::FunctionContextReturnTypeOmitted);
        }
    }

    super::super::setup::bootstrap_prepared_encoder(
        &mut encoder,
        ctx,
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
    )?;

    super::super::frame_state::declare_pre_state_variables(&mut encoder, &ctx.variables)?;

    // Alias framed collection variables before broadcasts and ground seeding.
    // ay-dpll can't propagate array equality through select (#2384), so making
    // framed post-state and pre-state the same ay term ensures the inductive
    // step proof is structurally trivial. Part of #2390.
    super::super::frame_state::alias_framed_collection_variables(
        &mut encoder,
        &ctx.variables,
        &modified_set,
    );

    encoder.add_broadcasts_for_inductive_step(ctx, Some(invariant))?;
    encoder.seed_collection_ground_selects()?; // #2390

    let mut eq_queue: Vec<TrustVcExpr> = Vec::new();

    let pre_typed = super::super::rewrite::replace_vars_with_pre_typed_with_targets(
        &invariant.expr,
        pre_state_targets,
    );
    encoder
        .add_typed_assumption(
            &format!("{}_pre", invariant.name),
            &pre_typed,
            Some(&mut eq_queue),
        )
        .map_err(|err| {
            super::wrap_setup_error(err, FRAME_SETUP_CONTEXT, |detail| {
                format!(
                    "Failed to assume pre-state invariant in inductive step: {}",
                    detail
                )
            })
        })?;

    for prior in verified_invariants {
        let prior_pre = super::super::rewrite::replace_vars_with_pre_typed_with_targets(
            &prior.expr,
            pre_state_targets,
        );
        encoder
            .add_typed_assumption(
                &format!("{}_prior_pre", prior.name),
                &prior_pre,
                Some(&mut eq_queue),
            )
            .map_err(|err| {
                super::wrap_setup_error(err, FRAME_SETUP_CONTEXT, |detail| {
                    format!(
                        "Failed to assume prior invariant '{}' pre-state in inductive step: {}",
                        prior.name, detail
                    )
                })
            })?;
    }

    if let Some(pre_guard) = pre_guard_expr {
        encoder
            .add_typed_assumption("loop_guard_pre", pre_guard, Some(&mut eq_queue))
            .map_err(|err| {
                super::wrap_setup_error(err, FRAME_SETUP_CONTEXT, |detail| {
                    format!("Failed to assume loop guard in inductive step: {}", detail)
                })
            })?;
    }

    super::super::frame_state::add_unmodified_frame_conditions(
        &mut encoder,
        &ctx.variables,
        &modified_set,
        &mut eq_queue,
        FRAME_SETUP_CONTEXT,
    )?;

    // FRAME-PRESERVED ASSUMPTIONS over UNMODIFIED variables.
    //
    // The inductive step bootstraps with `active_assumptions: &[]`, so the
    // function's body-level assumptions — chiefly its `#[requires]` clauses, which
    // the extractor lowers to `Assume` obligations named `precondition` — are
    // dropped. That wrongly havocs the loop-head value of an unmodified parameter
    // to something its precondition forbids (e.g. a `requires(step_eval >=
    // step_rhs)` over loop-INVARIANT parameters was ignored, refuting an otherwise
    // sound `acc_eval >= acc_rhs` invariant). SOUNDNESS of re-assuming a fact `P`
    // at every loop head: when ALL of `P`'s variables are UNMODIFIED by the loop
    // body, every such variable keeps a single value throughout the function (the
    // frame conditions above already pin `var == var_pre`), so `P` has the SAME
    // truth value at every program point — and it is taken as true somewhere (it
    // is an assumption), hence true at every loop head. We therefore re-assume
    // each `Assume`/`Requires`/`Recommends` obligation whose referenced variables
    // are DISJOINT from `modified_set`, rewritten to pre-state form like the
    // invariant and guard. Anything mentioning a modified var is skipped (it may
    // be false after iterations); `PostLoopAssume`/`BroadcastAssume`/`LoopGuard`
    // are handled by their own paths and excluded. Conservative and sound.
    for obligation in &ctx.obligations {
        // `Recommends` is ADVISORY and must NOT be re-assumed at loop heads (it is
        // a soft-warning check, never a hard hypothesis — see the primary partition
        // in prepared_context/validation.rs). Only genuine assumptions
        // (`Assume`/`Requires`) are re-assumed here.
        if !matches!(
            obligation.kind,
            ObligationKind::Assume | ObligationKind::Requires
        ) {
            continue;
        }
        let referenced = collect_referenced_var_names(&obligation.expr);
        if referenced.iter().any(|n| modified_set.contains(n.as_str())) {
            continue;
        }
        let pre_pred = super::super::rewrite::replace_vars_with_pre_typed_with_targets(
            &obligation.expr,
            pre_state_targets,
        );
        encoder
            .add_typed_assumption(
                &format!("{}_precond_frame", obligation.name),
                &pre_pred,
                Some(&mut eq_queue),
            )
            .map_err(|err| {
                super::wrap_setup_error(err, FRAME_SETUP_CONTEXT, |detail| {
                    format!(
                        "Failed to assume unmodified-var precondition '{}' in inductive step: {}",
                        obligation.name, detail
                    )
                })
            })?;
    }

    // Loop-body transition (M4): for each modified var with a captured
    // single-iteration transition, assume `var == rhs_pre`, where `var` is the
    // current (post-body) state and `rhs_pre` is the transition over pre-state
    // (loop-head) variables. This binds the otherwise-havoc'd current var to
    // `f(arbitrary pre-state)` — it NEVER ties the var to its pre-loop concrete
    // entry value, and is added ONLY for vars in `modified_set` (a framed var
    // already has `var == var_pre`, so binding it here would be redundant; the
    // guard keeps both paths from ever colliding). The current `var` term is
    // the same ay term the invariant goal reads, so the transition propagates
    // into the invariant check exactly like the unmodified frame equalities.
    for (var, ty, rhs_pre) in pre_transition_exprs {
        if !modified_set.contains(var.as_str()) {
            continue;
        }
        let transition_eq = TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(TrustVcExpr::Var {
                name: var.clone(),
                ty: ty.clone(),
            }),
            right: Box::new(rhs_pre.clone()),
        };
        encoder
            .add_typed_assumption(
                &format!("{}_body_transition", var),
                &transition_eq,
                Some(&mut eq_queue),
            )
            .map_err(|err| {
                super::wrap_setup_error(err, FRAME_SETUP_CONTEXT, |detail| {
                    format!(
                        "Failed to assume loop-body transition for '{}' in inductive step: {}",
                        var, detail
                    )
                })
            })?;
    }

    encoder.reconcile_equality_assumptions(&eq_queue)?;

    Ok(encoder)
}

/// Lowers a condition string to TrustVcExpr using the given TypeEnv.
fn lower_string_condition(condition: &str, env: &TypeEnv) -> TrustVcResult<TrustVcExpr> {
    let syn_expr: syn::Expr = syn::parse_str(condition).map_err(|source| TrustVcError::Parse {
        context: "parse inductive-step loop guard",
        source,
    })?;
    lower_syn_expr(&syn_expr, env).map_err(|source| TrustVcError::Lowering {
        context: "lower inductive-step loop guard",
        source,
    })
}
