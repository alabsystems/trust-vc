//! Logic selection for isolated overflow-check solvers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Logic;

use crate::ir::{TrustVcExpr, TrustVcType};
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
use crate::vc::{ObligationKind, SolverMode, VariableDecl};

/// Select the narrow native-BV route only for an entirely quantifier-free
/// Bool/BV verification context.
///
/// Overflow predicates are discharged in a fresh solver. Keeping that helper
/// on `Logic::All` made ay take its generic mixed-theory route even when the
/// resulting query contained only ground Bool/BV terms; for wide (BV128)
/// source-bound checks that route could consume the caller's whole deadline
/// before strict proof presentation. `QfBv` selects ay's native bit-blast and
/// source-certificate route without changing the deadline.
///
/// This predicate is intentionally an over-approximation in the safe direction:
/// any mixed sort, quantifier, UF-bearing expression, scoped proof construct, or
/// loop-state rewrite keeps `Logic::All`. A false negative costs performance;
/// a false positive could send a mixed query to the wrong theory route.
pub(super) fn isolated_overflow_logic(
    ctx: &PreparedVerificationContext,
    assertion: &PreparedObligation,
    use_int_for_measures: bool,
    post_loop_modified_vars: Option<&std::collections::HashSet<String>>,
    extra_variables: &[VariableDecl],
) -> Logic {
    if use_int_for_measures
        || post_loop_modified_vars.is_some()
        || ctx.has_collection_context
        || !ctx.helper_function_contexts.is_empty()
        || !ctx.trait_decls.is_empty()
        || !ctx.trait_impl_decls.is_empty()
        || !ctx.trait_impl_method_bodies.is_empty()
        || !ctx.trait_impl_method_ensures.is_empty()
        || !ctx.conformance_exempt_methods.is_empty()
        || !ctx.struct_types.is_empty()
        || !ctx.type_invariants.is_empty()
        || !ctx.assert_by_scopes.is_empty()
        || !ctx.loop_entry_scopes.is_empty()
        || !ctx.forall_bound_vars.is_empty()
        || !ctx.loop_guards.is_empty()
        || !ctx.loop_modified_vars.is_empty()
        || !ctx.loop_body_transitions.is_empty()
        || !ctx.broadcast_use_groups.is_empty()
        || !ctx.revealed_fns.is_empty()
        || !ctx.hidden_fns.is_empty()
        || !ctx.tracked_params.is_empty()
        || !ctx
            .variables
            .iter()
            .chain(extra_variables)
            .all(|variable| is_bool_or_bv_type(&variable.ty))
        || !ctx
            .function_context
            .as_ref()
            .is_none_or(is_bool_or_bv_function_context)
        || !ctx.obligations.iter().all(is_plain_bool_or_bv_obligation)
        || !is_plain_bool_or_bv_obligation(assertion)
    {
        Logic::All
    } else {
        Logic::QfBv
    }
}

fn is_bool_or_bv_function_context(function: &crate::vc::FunctionContext) -> bool {
    // A non-zero-arity function context is registered as an uninterpreted
    // function even when every argument/result is a bitvector.  That belongs
    // to QF_UFBV, not QF_BV.  A zero-arity function is just a constant and is
    // therefore still eligible for the native QF_BV helper.
    function.params().is_empty()
        && function.trait_bounds().is_empty()
        && is_bool_or_bv_type(function.return_type())
}

fn is_plain_bool_or_bv_obligation(obligation: &PreparedObligation) -> bool {
    matches!(
        obligation.kind,
        ObligationKind::Assert
            | ObligationKind::Assume
            | ObligationKind::Requires
            | ObligationKind::Ensures
            | ObligationKind::Recommends
    ) && obligation.bound_vars.is_none()
        && obligation.trigger_patterns.is_none()
        && obligation.prepared_triggers.is_none()
        && obligation.broadcast_guard.is_none()
        && obligation
            .solver_mode
            .is_none_or(|mode| matches!(mode, SolverMode::Default | SolverMode::BitVector))
        && is_bool_or_bv_expr(&obligation.expr)
}

fn is_bool_or_bv_type(ty: &TrustVcType) -> bool {
    matches!(
        ty,
        TrustVcType::Bool | TrustVcType::Int { .. } | TrustVcType::Uint { .. } | TrustVcType::Char
    )
}

fn is_bool_or_bv_expr(expr: &TrustVcExpr) -> bool {
    match expr {
        TrustVcExpr::BoolLit(_) => true,
        TrustVcExpr::IntLit { ty, .. }
        | TrustVcExpr::Var { ty, .. }
        | TrustVcExpr::IntConst { ty, .. } => is_bool_or_bv_type(ty),
        TrustVcExpr::Arith {
            left, right, ty, ..
        }
        | TrustVcExpr::SpecialArith {
            left, right, ty, ..
        }
        | TrustVcExpr::WrappingArith {
            left, right, ty, ..
        } => ty.bit_width().is_some() && is_bool_or_bv_expr(left) && is_bool_or_bv_expr(right),
        TrustVcExpr::Neg(inner) | TrustVcExpr::Not(inner) => is_bool_or_bv_expr(inner),
        TrustVcExpr::Compare { left, right, .. } | TrustVcExpr::Logic { left, right, .. } => {
            is_bool_or_bv_expr(left) && is_bool_or_bv_expr(right)
        }
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => is_bool_or_bv_expr(premise) && is_bool_or_bv_expr(conclusion),
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => {
            is_bool_or_bv_type(ty)
                && is_bool_or_bv_expr(cond)
                && is_bool_or_bv_expr(then_branch)
                && is_bool_or_bv_expr(else_branch)
        }
        TrustVcExpr::Let {
            ty, value, body, ..
        } => is_bool_or_bv_type(ty) && is_bool_or_bv_expr(value) && is_bool_or_bv_expr(body),
        TrustVcExpr::Cast {
            expr,
            from_ty,
            to_ty,
        } => is_bool_or_bv_type(from_ty) && is_bool_or_bv_type(to_ty) && is_bool_or_bv_expr(expr),
        // Every unclassified variant introduces (or may introduce) non-BV
        // sorts, quantifiers, UFs, datatype machinery, or fresh symbolic
        // state. Keep the generic route even if one instance returns Bool/BV.
        _ => false,
    }
}
