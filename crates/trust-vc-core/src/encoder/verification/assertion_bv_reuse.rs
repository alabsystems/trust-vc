//! Shared BV encoder fast-path for assertion verification.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Reuses a single BV encoder across multiple assertions when the solver
//! state is compatible (no nonlinear arithmetic, no termination measures).
//! Split from `assertion.rs` for the 500-line limit (#2621).

use std::collections::HashSet;
use std::panic::AssertUnwindSafe;

use super::assertion::convert_setup_error;
use super::assertion_timeout::{verify_assertion_with_timeout_reuse, ReuseAttempt};
use super::outcome::AssertionOutcome;
use super::overflow::check_overflow_predicates;
use super::panic::catch_encoding_panic_to_unknown;
use super::solve::demote_verified_outcome;
use super::VerificationSlices;
use crate::encoder::diagnostics::EncodingDiagnostics;
use crate::encoder::AYEncoder;
use crate::error::TrustVcResult;
use crate::ir::{TrustVcExpr, TrustVcType};
use crate::vc::ObligationKind;

use super::assertion::apply_collection_confirmation;

#[allow(clippy::large_enum_variant)]
pub(in crate::encoder) enum SharedBvFastPathAttempt {
    Reusable {
        encoder: AYEncoder,
        outcome: AssertionOutcome,
    },
    NonReusable(AssertionOutcome),
    TimedOut,
    Terminal(AssertionOutcome),
}

fn expr_contains_type_param(expr: &TrustVcExpr) -> bool {
    struct Visitor {
        found: bool,
    }

    impl crate::ir_expr_traversal::TrustVcExprVisitor for Visitor {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            if self.found {
                return;
            }
            if matches!(
                crate::ir_lowering::infer_expr_type(expr),
                TrustVcType::TypeParam(_)
            ) {
                self.found = true;
                return;
            }
            crate::ir_expr_traversal::walk_expr(self, expr);
        }
    }

    let mut visitor = Visitor { found: false };
    crate::ir_expr_traversal::TrustVcExprVisitor::visit_expr(&mut visitor, expr);
    visitor.found
}

/// True iff the prepared context carries any body-ordered `broadcast_use!`
/// activation marker ([`ObligationKind::BroadcastUse`]). Such a context has
/// POSITION-DEPENDENT grouped-broadcast activation, which the batch-wide shared
/// BV encoder cannot represent — see `can_use_shared_bv_fast_path`.
pub(in crate::encoder) fn context_has_broadcast_use_marker(
    ctx: &crate::prepared_context::PreparedVerificationContext,
) -> bool {
    ctx.obligations
        .iter()
        .any(|obligation| obligation.kind == ObligationKind::BroadcastUse)
}

pub(in crate::encoder) fn can_use_shared_bv_fast_path(
    assertion: &crate::prepared_context::PreparedObligation,
    context_has_collections: bool,
    context_has_broadcast_use_marker: bool,
) -> bool {
    // Collection-aware verification layers overflow prechecks and a
    // confirmation rerun on top of the main attempt. Keep those assertions on
    // fresh per-assertion encoders instead of stacking that work on a shared
    // reusable solver.
    !(context_has_collections
        // File-path `broadcast_use!` activation is POSITION-DEPENDENT: a grouped
        // broadcast axiom is active only for obligations at or after the marker.
        // The shared BV encoder is built ONCE with `assertion_focus = None`
        // (batch-wide) and reused across the batch, so it would drop every
        // position-activated grouped axiom (empty active-group snapshot) and
        // apply that stale set to EVERY assertion — a false Counterexample on a
        // genuinely-activated goal. Route these functions to the per-assertion
        // fallback, which rebuilds with the goal's own body position. Part of the
        // file-path broadcast_use! reinstatement.
        || context_has_broadcast_use_marker
        || assertion.expr.references_collection()
        || expr_contains_type_param(&assertion.expr)
        // Triggerless `forall|x| (… ∧ nested-quantifier ∧ …)`: the single-solve
        // refutation is unsound for this shape (round-4 quantifiers finding). Route
        // it to the per-assertion fallback, which discharges it via the sound
        // conjunct-split path (`try_verify_quantified_conjunction_split`).
        || super::split::is_quantified_conjunction_forall(&assertion.expr)
        || matches!(
            assertion.kind,
            ObligationKind::MeasureNonNegative | ObligationKind::MeasureDecreases
        )
        || matches!(
            assertion.solver_mode,
            Some(crate::vc::SolverMode::NonlinearArith)
        )
        // Hint-free nonlinear-REAL goal: must drop to the per-assertion
        // fallback so the Verus-faithful default-prover boundary in
        // `verify_single_assertion_typed_inner` refuses it as theory
        // INCOMPLETENESS (the `smt.arith.nl=false` analog) instead of the
        // shared encoder proving it via ay's bare NRA lane and silently
        // diverging from Verus (upstream real.rs `real_nonlinear2` pins the
        // hint-free failure). See
        // `nonlinear_real::unhinted_nonlinear_real_construct`.
        || (matches!(
            assertion.solver_mode,
            None | Some(crate::vc::SolverMode::Default)
        ) && super::nonlinear_real::unhinted_nonlinear_real_construct(&assertion.expr)
            .is_some()))
}

pub(in crate::encoder) fn verify_assertion_with_shared_bv_encoder(
    slices: &VerificationSlices<'_>,
    assertion: &crate::prepared_context::PreparedObligation,
    post_loop_modified_vars: Option<&HashSet<String>>,
    encoder: AYEncoder,
) -> TrustVcResult<SharedBvFastPathAttempt> {
    debug_assert!(
        can_use_shared_bv_fast_path(
            assertion,
            slices.ctx.has_collection_context,
            context_has_broadcast_use_marker(slices.ctx),
        ),
        "shared BV fast path only applies to default/BV regular assertions"
    );

    let post_loop = post_loop_modified_vars.cloned();
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        verify_assertion_with_shared_bv_encoder_inner(
            slices,
            assertion,
            post_loop.as_ref(),
            encoder,
        )
    }));
    match result {
        Ok(inner_result) => inner_result,
        Err(panic_info) => catch_encoding_panic_to_unknown(
            panic_info,
            "ay panic during encoding for",
            &assertion.name,
        )
        .map(SharedBvFastPathAttempt::Terminal),
    }
}

fn verify_assertion_with_shared_bv_encoder_inner(
    slices: &VerificationSlices<'_>,
    assertion: &crate::prepared_context::PreparedObligation,
    post_loop_modified_vars: Option<&HashSet<String>>,
    encoder: AYEncoder,
) -> TrustVcResult<SharedBvFastPathAttempt> {
    let ctx = slices.ctx;
    let mut run_diagnostics = EncodingDiagnostics::default();

    // BitVector mode (`assert by(bit_vector)`) wraps, so arithmetic carries no
    // overflow obligation; suppress arithmetic overflow predicates while still
    // running collection-precondition checks below.
    let arith_overflow_enabled = ctx.check_overflow()
        && !assertion
            .solver_mode
            .is_some_and(|m| m == crate::vc::SolverMode::BitVector)
        // Spec-predicate obligations (calc! steps, call-site precondition checks,
        // contract clauses) carry mathematical-int arithmetic, never overflow-checked
        // in Verus — same gate as the main path (#2778 spec-arith leak).
        && !super::assertion::obligation_carries_spec_arithmetic(assertion);

    // Collection precondition checks (nonempty, bounds) must run even when
    // check_overflow is false — may_emit_overflow_checks returns true for
    // CollectionOp/Index unconditionally.  The prior `ctx.check_overflow() &&`
    // gate caused these checks to be skipped in the shared BV fast path,
    // allowing tautologies like `s.first() == s.first()` on empty Seq to
    // verify spuriously.  Fixes #2506.
    if assertion
        .expr
        .may_emit_overflow_checks(arith_overflow_enabled)
    {
        let mut overflow_encoder =
            match AYEncoder::setup_from_prepared(slices, false, post_loop_modified_vars) {
                Ok(enc) => enc,
                Err(err) => return convert_setup_error(err).map(SharedBvFastPathAttempt::Terminal),
            };
        let overflow_outcome =
            check_overflow_predicates(&mut overflow_encoder, assertion, arith_overflow_enabled)?;
        run_diagnostics.merge(&overflow_encoder.state.diagnostics);
        if !matches!(overflow_outcome, AssertionOutcome::Verified) {
            return Ok(SharedBvFastPathAttempt::Terminal(overflow_outcome));
        }
    }

    match verify_assertion_with_timeout_reuse(encoder, assertion, ctx.rlimit_ms)? {
        ReuseAttempt::Completed { encoder, outcome } => {
            let outcome = apply_collection_confirmation(
                slices,
                assertion,
                outcome,
                false,
                post_loop_modified_vars,
                &[],
                None,
            )?;
            Ok(SharedBvFastPathAttempt::Reusable {
                encoder,
                outcome: demote_verified_outcome(outcome, &assertion.name, &run_diagnostics),
            })
        }
        ReuseAttempt::NonReusable { outcome } => Ok(SharedBvFastPathAttempt::NonReusable(outcome)),
        ReuseAttempt::TimedOut => Ok(SharedBvFastPathAttempt::TimedOut),
        ReuseAttempt::Panicked { outcome } => Ok(SharedBvFastPathAttempt::Terminal(outcome)),
    }
}
