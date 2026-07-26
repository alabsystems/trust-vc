// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::parse_solver_mode;
use crate::error::TrustVcError;
use crate::ir::TrustVcExpr;
use crate::proof_session::{self, try_with_session, try_with_session_mut};
use crate::vc::{
    ConditionOrigin, ObligationKind, ProofObligation, SolverMode, VerificationContext,
};
use std::collections::HashMap;
use syn::fold::{self, Fold};

/// Translate Rust syntax to SMT, falling back to raw Rust on encoder limitations
/// but never on parse failures from macro-generated `stringify!()` input (#1723).
pub(crate) fn translate_rust_to_smt(rust_expr: &str) -> String {
    try_with_session(
        |session| match session.translator.try_translate(rust_expr) {
            Ok(smt_expr) => smt_expr,
            Err(err @ TrustVcError::Parse { .. }) => unreachable!(
                "invariant: translate_rust_to_smt: expression from stringify!() is not \
                 valid Rust syntax: '{}': {} (#1723)",
                rust_expr, err
            ),
            Err(TrustVcError::Encoding { .. }) => rust_expr.to_string(),
            Err(err) => unreachable!(
                "invariant: translate_rust_to_smt encountered unexpected translator failure for \
                 '{}': {}",
                rust_expr, err
            ),
        },
    )
    // Graceful fallback on borrow conflict: return raw expression for
    // the encoder's AST parser to handle. Part of #1955, #2481.
    .unwrap_or_else(|_| rust_expr.to_string())
}

/// Pushes an obligation, recording borrow-conflict drops for fail-closed verification (#2360).
///
/// When the obligation is a `LoopInvariant` or `InvariantExceptBreak` and an
/// active loop context exists (pushed by auto-inferred range loop metadata),
/// the loop's modified-variable set and guard condition are automatically
/// applied to the invariant. Part of #2502.
pub(super) fn push_obligation(obligation: ProofObligation) {
    match try_with_session_mut(|s| {
        s.total_obligations_collected
            .set(s.total_obligations_collected.get() + 1);
        let kind = obligation.kind;
        let name = obligation.name.clone();
        let context = s.context.get_or_insert_with(VerificationContext::new);
        context.obligations.push(obligation);

        // Auto-apply loop metadata for loop invariants (#2502).
        if matches!(
            kind,
            ObligationKind::LoopInvariant | ObligationKind::InvariantExceptBreak
        ) {
            if let Some((modified_vars, guard)) = crate::loop_metadata::current_loop_context() {
                if !context.loop_modified_vars.contains_key(&name) {
                    context.set_loop_modified_vars(&name, modified_vars);
                    context.add_loop_guard(&name, &guard);
                }
            }
        }
    }) {
        Ok(()) => {}
        Err(_) => proof_session::record_obligation_drop(),
    }
}

/// Builds a `ProofObligation` with optional location.
fn build_obligation(
    name: String,
    condition: String,
    kind: ObligationKind,
    location: Option<String>,
    condition_origin: ConditionOrigin,
) -> ProofObligation {
    let mut obligation =
        ProofObligation::new(name, condition, kind).with_condition_origin(condition_origin);
    if let Some(loc) = location {
        obligation = obligation.with_location(loc);
    }
    obligation
}

struct LetBindingSubstituter<'a> {
    bindings: &'a HashMap<String, syn::Expr>,
}

impl Fold for LetBindingSubstituter<'_> {
    fn fold_expr(&mut self, expr: syn::Expr) -> syn::Expr {
        if let syn::Expr::Path(path) = &expr {
            if path.qself.is_none() && path.path.segments.len() == 1 {
                let name = path.path.segments[0].ident.to_string();
                if let Some(replacement) = self.bindings.get(&name) {
                    return replacement.clone();
                }
            }
        }
        fold::fold_expr(self, expr)
    }
}

fn parsed_local_let_bindings(session: &proof_session::ProofSession) -> HashMap<String, syn::Expr> {
    session
        .local_let_bindings
        .iter()
        .filter_map(|(name, init_expr)| {
            crate::chained_comparisons::parse_expr_str_with_chains(init_expr)
                .ok()
                .map(|expr| (name.clone(), expr))
        })
        .collect()
}

fn substitute_local_let_bindings(
    session: &proof_session::ProofSession,
    expr: syn::Expr,
) -> syn::Expr {
    if session.local_let_bindings.is_empty() {
        return expr;
    }
    let bindings = parsed_local_let_bindings(session);
    if bindings.is_empty() {
        return expr;
    }
    LetBindingSubstituter {
        bindings: &bindings,
    }
    .fold_expr(expr)
}

fn lower_condition_with_session(
    session: &proof_session::ProofSession,
    raw_condition: &str,
    env: &crate::ir_lowering::TypeEnv,
) -> Option<TrustVcExpr> {
    let syn_expr = crate::chained_comparisons::parse_expr_str_with_chains(raw_condition).ok()?;
    let syn_expr = substitute_local_let_bindings(session, syn_expr);
    crate::ir_lowering::lower_syn_expr(&syn_expr, env).ok()
}

/// Attempts to parse and lower a raw Rust condition against the current
/// proof-session type environment. Returns the lowered `TrustVcExpr` on
/// success, or `None` if there is no active session, no context, or the
/// parse/lowering fails (so the legacy translator fallback remains available).
/// Fixes #2584.
fn try_lower_current_condition(raw_condition: &str) -> Option<TrustVcExpr> {
    try_with_session(|session| {
        let context = session.context.as_ref()?;
        let env = crate::prepared_context::build_type_env(context).ok()?;
        let syn_expr =
            crate::chained_comparisons::parse_expr_str_with_chains(raw_condition).ok()?;
        crate::ir_lowering::lower_syn_expr(&syn_expr, &env).ok()
    })
    .ok()
    .flatten()
}

/// Collects a proof obligation, preferring the typed-cache path over
/// legacy string translation. If the raw Rust condition can be parsed
/// and lowered against the current session's type environment, the
/// lowered `TrustVcExpr` is cached and the raw condition string is
/// stored on the obligation. Otherwise falls back to
/// `translate_rust_to_smt`. Fixes #2584.
fn collect_obligation_prefer_typed(
    kind: ObligationKind,
    name: String,
    raw_condition: String,
    location: Option<String>,
    solver_mode: Option<SolverMode>,
) {
    let effective_solver_mode = effective_solver_mode(solver_mode);
    if let Some(expr) = try_lower_current_condition(&raw_condition) {
        cache_pre_built_expr(name.clone(), raw_condition.clone(), expr);
        let mut obligation = build_obligation(
            name,
            raw_condition,
            kind,
            location,
            ConditionOrigin::LoweredFromCondition,
        );
        if let Some(mode) = effective_solver_mode {
            obligation = obligation.with_solver_mode(mode);
        }
        push_obligation(obligation);
        return;
    }

    // Fallback: legacy string translation
    let translated = translate_rust_to_smt(&raw_condition);
    let mut obligation = build_obligation(
        name,
        translated,
        kind,
        location,
        ConditionOrigin::LegacyTranslatedString,
    );
    if let Some(mode) = effective_solver_mode {
        obligation = obligation.with_solver_mode(mode);
    }
    push_obligation(obligation);
}

fn effective_solver_mode(explicit: Option<SolverMode>) -> Option<SolverMode> {
    explicit.or_else(proof_session::current_function_solver_mode)
}

/// Collects a proof obligation in the active proof session.
pub fn collect_obligation(
    kind: ObligationKind,
    name: String,
    condition: String,
    location: Option<String>,
) {
    collect_obligation_prefer_typed(kind, name, condition, location, None);
}

/// Collects a proof obligation with solver mode. Part of #2144.
pub fn collect_solver_mode_obligation(
    kind: ObligationKind,
    name: String,
    condition: String,
    location: Option<String>,
    solver_mode: &str,
) {
    let mode = parse_solver_mode(solver_mode);
    collect_obligation_prefer_typed(kind, name, condition, location, Some(mode));
}

/// Collects a typed proof obligation (AST string from syn parsing).
pub fn collect_typed_obligation(
    kind: ObligationKind,
    name: String,
    ast_string: String,
    location: Option<String>,
) {
    collect_obligation_prefer_typed(kind, name, ast_string, location, None);
}

/// Collects an extensional equality/inequality obligation from two
/// individually-stringified arguments. Parses and lowers each argument
/// independently, avoiding the whole-macro stringification round-trip
/// that breaks turbofish generics inside `ext_eq!`/`ext_ne!`. Part of #2658.
pub fn collect_ext_eq_obligation(
    kind: ObligationKind,
    name: String,
    lhs_condition: String,
    rhs_condition: String,
    is_eq: bool,
    location: Option<String>,
) {
    // Use macro syntax (`ext_eq!`) so the preparation-time lowerer dispatches
    // to `lower_macro_expr` which already handles ext_eq!/ext_ne! correctly.
    // Function-call syntax (`ext_eq(...)`) would be parsed as an unknown function.
    let display = if is_eq {
        format!("ext_eq!({lhs_condition}, {rhs_condition})")
    } else {
        format!("ext_ne!({lhs_condition}, {rhs_condition})")
    };

    if let Some(expr) = try_lower_ext_eq_parts(&lhs_condition, &rhs_condition, is_eq) {
        collect_obligation_expr(kind, name, display, expr, location);
        return;
    }

    // Fallback: store the display string for preparation-time lowering.
    collect_obligation_prefer_typed(kind, name, display, location, None);
}

/// Parses and lowers two ext_eq/ext_ne argument strings individually,
/// then combines via `build_ext_eq_expr` / `build_ext_ne_expr`.
fn try_lower_ext_eq_parts(
    lhs_condition: &str,
    rhs_condition: &str,
    is_eq: bool,
) -> Option<TrustVcExpr> {
    try_with_session(|session| {
        let context = session.context.as_ref()?;
        let env = crate::prepared_context::build_type_env(context).ok()?;
        let lhs = lower_condition_with_session(session, lhs_condition, &env)?;
        let rhs = lower_condition_with_session(session, rhs_condition, &env)?;
        if is_eq {
            Some(crate::extensional_eq::build_ext_eq_expr(lhs, rhs))
        } else {
            Some(crate::extensional_eq::build_ext_ne_expr(lhs, rhs))
        }
    })
    .ok()
    .flatten()
}

/// Collects a pre-built typed obligation, caching its `TrustVcExpr` (#1866).
pub fn collect_obligation_expr(
    kind: ObligationKind,
    name: String,
    condition_display: String,
    expr: TrustVcExpr,
    location: Option<String>,
) {
    cache_pre_built_expr(name.clone(), condition_display.clone(), expr);
    let mut obligation = build_obligation(
        name,
        condition_display,
        kind,
        location,
        ConditionOrigin::PreBuiltExprCache,
    );
    if let Some(mode) = effective_solver_mode(None) {
        obligation = obligation.with_solver_mode(mode);
    }
    push_obligation(obligation);
}

/// Collects a pre-built typed obligation with solver mode (#1866).
pub fn collect_solver_mode_obligation_expr(
    kind: ObligationKind,
    name: String,
    condition_display: String,
    expr: TrustVcExpr,
    location: Option<String>,
    solver_mode: &str,
) {
    cache_pre_built_expr(name.clone(), condition_display.clone(), expr);
    let mode = parse_solver_mode(solver_mode);
    let mut obligation = build_obligation(
        name,
        condition_display,
        kind,
        location,
        ConditionOrigin::PreBuiltExprCache,
    );
    obligation = obligation.with_solver_mode(mode);
    push_obligation(obligation);
}

/// Caches a pre-built `TrustVcExpr` without creating an obligation (#1866).
pub fn cache_pre_built_expr(name: String, condition_display: String, expr: TrustVcExpr) {
    let _ = try_with_session_mut(|session| {
        session
            .pre_built_exprs
            .insert((name, condition_display), expr);
    });
}

/// Takes a pre-built `TrustVcExpr` from the cache (remove-on-read).
pub(crate) fn take_pre_built_expr(name: &str, condition: &str) -> Option<TrustVcExpr> {
    try_with_session_mut(|session| {
        session
            .pre_built_exprs
            .remove(&(name.to_string(), condition.to_string()))
    })
    .ok()
    .flatten()
}

/// Clears the pre-built expression cache for direct cache-lifecycle tests.
#[cfg(test)]
pub(crate) fn clear_pre_built_exprs() {
    // Graceful skip on borrow conflict (cleanup path). Part of #1955.
    let _ = try_with_session_mut(|session| {
        session.pre_built_exprs.clear();
    });
}

/// Records that obligation collection silently failed due to a borrow conflict.
pub(crate) fn record_obligation_drop() {
    proof_session::record_obligation_drop();
}

/// Returns the number of obligations dropped in the current verification scope.
pub(crate) fn obligations_dropped_count() -> usize {
    proof_session::obligations_dropped_count()
}

/// Clears the dropped-obligation counter for the current verification scope.
pub(crate) fn reset_obligations_dropped() {
    proof_session::reset_obligations_dropped();
}

/// Restores the dropped-obligation counter for the current verification scope.
pub(crate) fn set_obligations_dropped_count(count: usize) {
    proof_session::set_obligations_dropped_count(count);
}

/// Returns the monotonic count of successfully collected obligations in this thread.
/// Dropped obligations are excluded so diagnostics match the actual context (#1713, #2360).
pub fn total_obligations_collected() -> u64 {
    try_with_session(|session| session.total_obligations_collected.get()).unwrap_or(0)
}
