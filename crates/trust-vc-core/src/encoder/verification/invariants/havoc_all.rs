//! Havoc-all inductive-step verification.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::AssertionOutcome;
use crate::encoder::AYEncoder;
use crate::error::TrustVcResult;
use crate::ir::TrustVcExpr;
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};

const HAVOC_SETUP_CONTEXT: &str = "build havoc-all inductive-step encoder";

/// Mode 1 typed: Havoc-all inductive step (tautology check).
/// All variables are unconstrained; previously verified invariants remain
/// assumed at the loop head.
pub(super) fn verify_inductive_step_havoc_all_typed(
    ctx: &PreparedVerificationContext,
    invariant: &PreparedObligation,
    verified_invariants: &[&PreparedObligation],
) -> TrustVcResult<AssertionOutcome> {
    super::run_inductive_verification(ctx, invariant, || {
        setup_havoc_all_encoder(ctx, invariant, verified_invariants)
    })
}

/// Build a configured encoder for havoc-all inductive step.
///
/// Extracted so it can be called twice: once for overflow checking
/// (discarded) and once for the main assertion. Part of #2246.
fn setup_havoc_all_encoder(
    ctx: &PreparedVerificationContext,
    invariant: &PreparedObligation,
    verified_invariants: &[&PreparedObligation],
) -> TrustVcResult<AYEncoder> {
    // Second solver instance; same envelope as the top-level encoder so the
    // deterministic budget is not silently absent on the havoc-all lane.
    let wall_backstop_ms = ctx
        .rlimit_ms
        .unwrap_or(crate::encoder::verification::timeout::DEFAULT_SOLVER_WALL_BACKSTOP_MS);
    let conflict_budget =
        crate::encoder::verification::timeout::effective_conflict_budget(ctx.rlimit_conflicts);
    let mut encoder = AYEncoder::new().with_limits(wall_backstop_ms, conflict_budget, 512);
    let broadcast_assumptions: Vec<_> = ctx
        .obligations
        .iter()
        .filter(|obligation| matches!(obligation.kind, crate::vc::ObligationKind::BroadcastAssume))
        .collect();
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

    encoder.add_broadcasts_for_inductive_step(ctx, Some(invariant))?;
    encoder.seed_collection_ground_selects()?; // #2390

    let mut eq_queue: Vec<TrustVcExpr> = Vec::new();
    for prior in verified_invariants {
        encoder
            .add_typed_assumption(
                &format!("{}_prior", prior.name),
                &prior.expr,
                Some(&mut eq_queue),
            )
            .map_err(|err| {
                super::wrap_setup_error(err, HAVOC_SETUP_CONTEXT, |detail| {
                    format!(
                        "Failed to assume prior invariant '{}' in havoc-all inductive step: {}",
                        prior.name, detail
                    )
                })
            })?;
    }
    encoder.reconcile_equality_assumptions(&eq_queue)?;

    Ok(encoder)
}
