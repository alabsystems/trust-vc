//! Test-time verification support for trust_vc macros.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides thread-local collection of verification conditions
//! and a verify_markers! macro for test-time verification via ay.
//!
//! FILE OWNERSHIP: W1 owns this file exclusively per issue #755.
//! Other workers should file issues for needed changes.

use crate::proof_session::{try_with_session, try_with_session_mut, AssertByScope};
use crate::vc::{ObligationKind, ProofObligation, VariableDecl, VerificationContext};

// Re-export broadcast_state functions for backward compatibility.
// External callers (broadcast.rs generated code, tests) use these paths.
#[doc(hidden)]
pub use crate::broadcast_state::{
    is_in_broadcast_mode, register_broadcast_lemma, register_trigger, set_broadcast_mode,
    BroadcastGuard,
};

// Re-export decreases_runtime functions for backward compatibility.
// Tests and the verify_proof! macro use these paths.
#[doc(hidden)]
pub use crate::decreases_runtime::{
    collect_decrease_obligation, collect_decreases_measure, collect_loop_decreases_measure,
    verify_decreases, verify_proof_impl,
};
// Re-export marker_extraction functions for backward compatibility.
// The verify_markers! macro uses this path.
#[doc(hidden)]
pub use crate::marker_extraction::verify_markers_impl;

// Re-export obligation_collection functions for backward compatibility.
// Existing generated code calls these paths via verify_macro::.
#[doc(hidden)]
pub use crate::obligation_collection::{
    cache_pre_built_expr, collect_ext_eq_obligation, collect_final_value,
    collect_final_value_deref, collect_let_binding, collect_let_binding_runtime_value,
    collect_let_binding_runtime_value_i128, collect_let_binding_runtime_value_u128,
    collect_obligation, collect_obligation_expr, collect_old_value, collect_old_value_deref,
    collect_solver_mode_obligation, collect_solver_mode_obligation_expr, collect_typed_obligation,
    collect_variable, collect_variable_from_ref, collect_variable_runtime, lookup_var_type,
    register_tracked_param, total_obligations_collected, track_local_variable,
};

// Re-export loop_metadata functions for proc-macro generated code.
// The auto-inferred range loop fold pass emits push/pop calls via
// ::trust_vc_core::loop_metadata:: directly, but this alias keeps the
// verify_macro:: path available for consistency. Part of #2502.
#[doc(hidden)]
pub use crate::loop_metadata::{pop_loop_context, push_loop_context};

// Re-export context_management functions/types for backward compatibility.
// Existing generated code and tests call these paths via verify_macro::.
#[doc(hidden)]
pub use crate::context_management::{
    clear_all_thread_locals, clear_context, get_context, restore_context, save_context_guard,
    take_context, ContextGuard,
};

// Thread-local block removed — all state consolidated into proof_session::PROOF_SESSION.
// Part of #2481 Slice 1.

/// Sets whether we're currently in proof mode.
///
/// In proof mode, assertions only collect obligations without runtime checks.
#[doc(hidden)]
pub fn set_proof_mode(mode: bool) {
    let _ = try_with_session_mut(|s| {
        s.in_proof_mode = mode;
    });
}

/// Returns whether we're currently in proof mode.
#[doc(hidden)]
pub fn is_in_proof_mode() -> bool {
    try_with_session(|s| s.in_proof_mode).unwrap_or(false)
}

/// Guard returned by `enter_function_solver_mode_scope`.
#[doc(hidden)]
#[must_use = "FunctionSolverModeGuard restores the previous solver mode on drop"]
pub struct FunctionSolverModeGuard {
    saved_mode: Option<Option<crate::vc::SolverMode>>,
}

impl Drop for FunctionSolverModeGuard {
    fn drop(&mut self) {
        if let Some(saved_mode) = self.saved_mode.take() {
            let _ = try_with_session_mut(|s| {
                s.function_solver_mode = saved_mode;
            });
        }
    }
}

/// Sets an ambient solver mode for obligations collected in a proof function.
#[doc(hidden)]
pub fn enter_function_solver_mode_scope(mode: crate::vc::SolverMode) -> FunctionSolverModeGuard {
    let saved_mode = try_with_session_mut(|s| {
        let saved = s.function_solver_mode;
        s.function_solver_mode = Some(mode);
        saved
    })
    .ok();

    FunctionSolverModeGuard { saved_mode }
}

/// Sets the invariant mask on the current verification context.
///
/// Called by the expanded `#[opens_invariants]` attribute to restrict which
/// invariant namespaces may be opened within the function body.
/// Part of #2427 Slice 4.
#[doc(hidden)]
pub fn set_invariant_mask(mask: crate::vc::InvariantMask) {
    let _ = try_with_session_mut(|s| {
        let context = s.context.get_or_insert_with(VerificationContext::new);
        context.set_invariant_mask(mask);
    });
}

/// Pushes a Reveal obligation for the named function into the current context.
///
/// Called by the expanded `reveal!()` macro. Makes an opaque spec function's
/// body axiom available in the current verification query. Part of #1901.
#[doc(hidden)]
pub fn push_reveal(fn_name: &str) {
    if is_in_proof_mode() {
        let _ = try_with_session_mut(|s| {
            let context = s.context.get_or_insert_with(VerificationContext::new);
            context
                .obligations
                .push(crate::vc::ProofObligation::reveal(fn_name));
        });
    }
}

/// Records a `hide!()` directive for the named function in the current context.
///
/// Called by the expanded `hide!()` macro. Suppresses the function's defining
/// body axiom for the current verification query — the function becomes
/// strictly uninterpreted, exactly like an unrevealed `#[trust_vc::opaque]`
/// spec fn — unless the same proof also `reveal!`s it (reveal wins over hide).
/// Mirrors Verus's `hide(f)` per-function fuel directive.
#[doc(hidden)]
pub fn push_hide(fn_name: &str) {
    if is_in_proof_mode() {
        let _ = try_with_session_mut(|s| {
            let context = s.context.get_or_insert_with(VerificationContext::new);
            // Populate `hidden_fns` (unchanged semantics for the no-reveal case:
            // the body stays uninterpreted query-wide).
            context.hide_function(fn_name);
            // ALSO push a body-ordered Hide obligation so
            // `reject_unsound_hide_reveal_interleave` (prepare()) can see this
            // hide's position relative to checked obligations and the closing
            // reveal!. Without it the session path shares the file path's
            // former hole: `hide!(f); assert!(<provable via f's body>);
            // reveal!(f)` VERIFIED under the query-granular reveal-wins model
            // while Verus refutes it (f hidden at the assert) — a
            // proves-more-than-Verus false-verify. Part of #2785.
            context
                .obligations
                .push(crate::vc::ProofObligation::hide(fn_name));
        });
    }
}

/// Begins an assert_by scope. Records the current obligation count so that
/// obligations collected during the proof block can be extracted later.
///
/// Called by the expanded assert_by! macro before executing the proof block.
/// Fixes #1547: implements scope isolation for assert_by! proof blocks.
#[doc(hidden)]
pub fn begin_assert_by_scope(name: String) {
    begin_assert_by_scope_with_label(name, None);
}

/// Begins an assert_by scope with an explicit display label.
///
/// When `label` is `Some`, the resulting obligation carries `ProofStepMeta`
/// so counterexample diagnostics show the label instead of the internal key.
/// Used by `calc!` to emit per-step labels like "calc step 1 of 3".
/// Part of #2652.
#[doc(hidden)]
pub fn begin_assert_by_scope_with_label(name: String, label: Option<String>) {
    // Graceful skip on borrow conflict: scope not pushed → end_assert_by_scope
    // falls back to regular Assert via the None path. Part of #1955.
    let _ = try_with_session_mut(|s| {
        let obligation_count = s.context.as_ref().map_or(0, |c| c.obligations.len());
        s.assert_by_scope_stack.push(AssertByScope::new(
            name,
            label,
            obligation_count,
            s.local_let_bindings.clone(),
        ));
    });
}

/// Inner scope-end logic: pops the scope stack, drains scoped obligations, and
/// creates the AssertBy obligation with the given condition string (already
/// translated or raw). Extracted as Step 3c helper to avoid translating twice.
fn end_assert_by_scope_inner(
    condition_for_obligation: String,
    fallback_condition: Option<String>,
    location: Option<String>,
    solver_mode: Option<crate::vc::SolverMode>,
) {
    let effective_solver_mode =
        solver_mode.or_else(crate::proof_session::current_function_solver_mode);
    // Graceful skip on borrow conflict: returns None → triggers the
    // fallback path to regular Assert. Part of #1955.
    let scope_info = try_with_session_mut(|s| s.assert_by_scope_stack.pop())
        .ok()
        .flatten();

    let Some(scope_info) = scope_info else {
        // No scope to end — fall back to regular Assert (backward compat).
        // This path is reached when end_assert_by_scope is called without a
        // matching begin_assert_by_scope, OR on borrow conflict (#1955).
        let cond = fallback_condition.unwrap_or(condition_for_obligation);
        if let Some(mode) = effective_solver_mode {
            crate::obligation_collection::collect_solver_mode_obligation(
                ObligationKind::Assert,
                "assert_by_fallback".to_string(),
                cond,
                location,
                match mode {
                    crate::vc::SolverMode::BitVector => "bit_vector",
                    crate::vc::SolverMode::NonlinearArith => "nonlinear_arith",
                    crate::vc::SolverMode::Compute => "compute",
                    crate::vc::SolverMode::Default => "",
                    #[allow(unreachable_patterns)]
                    _ => "",
                },
            );
        } else {
            collect_obligation(
                ObligationKind::Assert,
                "assert_by_fallback".to_string(),
                cond,
                location,
            );
        }
        return;
    };

    let _ = try_with_session_mut(|s| {
        let scope_name = scope_info.scope_key;
        let context = s.context.get_or_insert_with(VerificationContext::new);

        // Extract obligations added during the proof block
        let scoped: Vec<ProofObligation> =
            if scope_info.obligation_start_index < context.obligations.len() {
                context
                    .obligations
                    .drain(scope_info.obligation_start_index..)
                    .collect()
            } else {
                Vec::new()
            };
        s.local_let_bindings = scope_info.saved_local_let_bindings;

        // Add the scoped assert_by with the provided condition
        context.add_assert_by_with_solver_mode(
            &scope_name,
            &condition_for_obligation,
            scoped,
            effective_solver_mode,
        );

        // Set step_meta and location on the AssertBy obligation (last obligation).
        // Part of #2652.
        if let Some(last) = context.obligations.last_mut() {
            if let Some(label) = scope_info.display_label {
                last.step_meta = Some(crate::vc::ProofStepMeta::new(scope_name.clone(), label));
            }
            if let Some(loc) = location {
                last.location = Some(loc);
            }
        }
    });
}

/// Ends an assert_by scope. Extracts proof block obligations, removes them from
/// the main obligation list, and creates an AssertBy obligation with scoped
/// assumptions. The encoder's verified_assert_by vector makes the proven
/// condition available for subsequent assertions (no _proven Assume needed).
///
/// Called by the expanded assert_by! macro after the proof block and condition
/// collection. Fixes #1547, #1642.
#[doc(hidden)]
pub fn end_assert_by_scope(condition: String, location: Option<String>) {
    // Translate the condition with the shared obligation translator.
    let translated = crate::obligation_collection::translate_rust_to_smt(&condition);
    end_assert_by_scope_inner(translated, Some(condition), location, None);
}

/// Ends an assert_by scope with a solver-mode override.
#[doc(hidden)]
pub fn end_assert_by_scope_with_solver_mode(
    condition: String,
    location: Option<String>,
    solver_mode: crate::vc::SolverMode,
) {
    let translated = crate::obligation_collection::translate_rust_to_smt(&condition);
    end_assert_by_scope_inner(translated, Some(condition), location, Some(solver_mode));
}

/// Ends an assert_by scope with a pre-built TrustVcExpr (Phase 5 Step 3c).
///
/// Caches the TrustVcExpr keyed by `(scope_name, condition_display)`, then
/// completes the scope using the raw AST string (no translation). This ensures
/// `ProofObligation.condition` matches the cache key for `prepare_context` lookup.
///
/// Part of #1866: completes the dual-path for assert_by! scoped assertions.
#[doc(hidden)]
pub fn end_assert_by_scope_expr(
    condition_display: String,
    expr: crate::ir::TrustVcExpr,
    location: Option<String>,
) {
    // Peek at the scope name from the stack (without popping) for the cache key.
    let scope_name = try_with_session(|s| {
        s.assert_by_scope_stack
            .last()
            .map(|scope| scope.scope_key.clone())
    })
    .ok()
    .flatten();

    let cache_name = scope_name.unwrap_or_else(|| "assert_by_fallback".to_string());
    crate::obligation_collection::cache_pre_built_expr(cache_name, condition_display.clone(), expr);

    // Use raw AST string — no translation. The TrustVcExpr is cached above.
    end_assert_by_scope_inner(condition_display, None, location, None);
}

/// Ends an assert_by scope with a pre-built TrustVcExpr and solver-mode override.
#[doc(hidden)]
pub fn end_assert_by_scope_expr_with_solver_mode(
    condition_display: String,
    expr: crate::ir::TrustVcExpr,
    location: Option<String>,
    solver_mode: crate::vc::SolverMode,
) {
    let scope_name = try_with_session(|s| {
        s.assert_by_scope_stack
            .last()
            .map(|scope| scope.scope_key.clone())
    })
    .ok()
    .flatten();

    let cache_name = scope_name.unwrap_or_else(|| "assert_by_fallback".to_string());
    crate::obligation_collection::cache_pre_built_expr(cache_name, condition_display.clone(), expr);

    end_assert_by_scope_inner(condition_display, None, location, Some(solver_mode));
}

/// Begins an `assert_forall_by!` scope.
///
/// This is the quantified analogue of `begin_assert_by_scope`: proof-block
/// obligations are scoped, and `bound_vars` are recorded on the context so the
/// AssertBy obligation is verified under those variables and replayed as a
/// quantified fact after it succeeds.
#[doc(hidden)]
pub fn begin_assert_forall_by_scope(
    name: String,
    bound_vars: Vec<(String, crate::ir::TrustVcType)>,
) {
    let _ = try_with_session_mut(|s| {
        let obligation_count = s.context.as_ref().map_or(0, |c| c.obligations.len());
        let context = s.context.get_or_insert_with(VerificationContext::new);
        assert!(
            !context.assert_by_scopes.contains_key(&name)
                && !context.forall_bound_vars.contains_key(&name),
            "invariant: duplicate assert_forall_by scope name `{name}`"
        );

        let decls = bound_vars
            .into_iter()
            .map(|(name, ty)| VariableDecl {
                bounded_len: false,
                name,
                ty,
            })
            .collect();
        context.forall_bound_vars.insert(name.clone(), decls);
        s.assert_by_scope_stack.push(AssertByScope::new(
            name,
            None,
            obligation_count,
            s.local_let_bindings.clone(),
        ));
    });
}

fn end_assert_forall_by_scope_inner(
    condition_for_obligation: String,
    fallback_condition: Option<String>,
    location: Option<String>,
    solver_mode: Option<crate::vc::SolverMode>,
    trigger_patterns: Option<Vec<Vec<String>>>,
) {
    let effective_solver_mode =
        solver_mode.or_else(crate::proof_session::current_function_solver_mode);
    let scope_info = try_with_session_mut(|s| s.assert_by_scope_stack.pop())
        .ok()
        .flatten();

    let Some(scope_info) = scope_info else {
        let cond = fallback_condition.unwrap_or(condition_for_obligation);
        if let Some(mode) = effective_solver_mode {
            crate::obligation_collection::collect_solver_mode_obligation(
                ObligationKind::Assert,
                "assert_forall_by_fallback".to_string(),
                cond,
                location,
                match mode {
                    crate::vc::SolverMode::BitVector => "bit_vector",
                    crate::vc::SolverMode::NonlinearArith => "nonlinear_arith",
                    crate::vc::SolverMode::Compute => "compute",
                    crate::vc::SolverMode::Default => "",
                    #[allow(unreachable_patterns)]
                    _ => "",
                },
            );
        } else {
            collect_obligation(
                ObligationKind::Assert,
                "assert_forall_by_fallback".to_string(),
                cond,
                location,
            );
        }
        return;
    };

    let _ = try_with_session_mut(|s| {
        let scope_name = scope_info.scope_key;
        let context = s.context.get_or_insert_with(VerificationContext::new);

        let scoped: Vec<ProofObligation> =
            if scope_info.obligation_start_index < context.obligations.len() {
                context
                    .obligations
                    .drain(scope_info.obligation_start_index..)
                    .map(|obligation| match effective_solver_mode {
                        Some(mode) if obligation.kind == ObligationKind::Requires => {
                            obligation.with_solver_mode(mode)
                        }
                        _ => obligation,
                    })
                    .collect()
            } else {
                Vec::new()
            };
        s.local_let_bindings = scope_info.saved_local_let_bindings;

        let bound_var_names = context
            .forall_bound_vars
            .get(&scope_name)
            .map(|decls| decls.iter().map(|decl| decl.name.clone()).collect())
            .unwrap_or_default();

        assert!(
            !context.assert_by_scopes.contains_key(&scope_name),
            "invariant: duplicate assert_forall_by scope name `{scope_name}`"
        );
        context.assert_by_scopes.insert(scope_name.clone(), scoped);

        let mut obligation =
            ProofObligation::assert_by(scope_name.clone(), condition_for_obligation)
                .with_bound_vars(bound_var_names);
        if let Some(patterns) = trigger_patterns.filter(|patterns| !patterns.is_empty()) {
            obligation = obligation.with_trigger_patterns(patterns);
        }
        if let Some(mode) = effective_solver_mode {
            obligation = obligation.with_solver_mode(mode);
        }
        if let Some(loc) = location {
            obligation = obligation.with_location(loc);
        }
        if let Some(label) = scope_info.display_label {
            obligation =
                obligation.with_step_meta(crate::vc::ProofStepMeta::new(scope_name.clone(), label));
        }
        context.obligations.push(obligation);
    });
}

/// Ends an `assert_forall_by!` scope using source-text lowering.
#[doc(hidden)]
pub fn end_assert_forall_by_scope(condition: String, location: Option<String>) {
    end_assert_forall_by_scope_with_triggers(condition, location, Vec::new());
}

/// Ends an `assert_forall_by!` scope using source-text lowering and explicit trigger patterns.
#[doc(hidden)]
pub fn end_assert_forall_by_scope_with_triggers(
    condition: String,
    location: Option<String>,
    trigger_patterns: Vec<Vec<String>>,
) {
    let translated = crate::obligation_collection::translate_rust_to_smt(&condition);
    end_assert_forall_by_scope_inner(
        translated,
        Some(condition),
        location,
        None,
        Some(trigger_patterns),
    );
}

/// Ends an `assert_forall_by!` scope using a pre-built body expression.
#[doc(hidden)]
pub fn end_assert_forall_by_scope_expr(
    condition_display: String,
    expr: crate::ir::TrustVcExpr,
    location: Option<String>,
) {
    end_assert_forall_by_scope_expr_with_triggers(condition_display, expr, location, Vec::new());
}

/// Ends an `assert_forall_by!` scope using a pre-built body expression and explicit trigger patterns.
#[doc(hidden)]
pub fn end_assert_forall_by_scope_expr_with_triggers(
    condition_display: String,
    expr: crate::ir::TrustVcExpr,
    location: Option<String>,
    trigger_patterns: Vec<Vec<String>>,
) {
    let scope_name = try_with_session(|s| {
        s.assert_by_scope_stack
            .last()
            .map(|scope| scope.scope_key.clone())
    })
    .ok()
    .flatten();

    let cache_name = scope_name.unwrap_or_else(|| "assert_forall_by_fallback".to_string());
    crate::obligation_collection::cache_pre_built_expr(cache_name, condition_display.clone(), expr);

    end_assert_forall_by_scope_inner(
        condition_display,
        None,
        location,
        None,
        Some(trigger_patterns),
    );
}

/// Opens a local invariant scope for verification.
///
/// Called by the expanded `open_local_invariant!` macro. Records the invariant
/// reference and binding name so the encoder can:
/// 1. Havoc the inner variable (fresh symbolic value)
/// 2. Assume the predicate holds at entry
/// 3. Process the body (which may modify `inner`)
/// 4. Assert the predicate holds at exit (via `end_invariant_open`)
///
/// `namespace` carries the invariant's namespace for mask enforcement.
/// Part of #2427 Slice 4.
#[doc(hidden)]
pub fn begin_invariant_open(
    invariant_ref: String,
    binding_name: String,
    namespace: Option<i64>,
    location: Option<String>,
) {
    let mut obligation = ProofObligation::new(
        format!("invariant_open_{binding_name}"),
        format!("__trust_vc_invariant_open({invariant_ref}, {binding_name})"),
        ObligationKind::InvariantOpen,
    );
    if let Some(loc) = location {
        obligation = obligation.with_location(loc);
    }
    if let Some(ns) = namespace {
        obligation = obligation.with_invariant_namespace(ns);
    }
    let _ = try_with_session_mut(|s| {
        s.context
            .get_or_insert_with(VerificationContext::new)
            .push_obligation(obligation);
    });
}

/// Closes a local invariant scope for verification.
///
/// Called by the expanded `open_local_invariant!` macro after the body block.
/// The encoder asserts the invariant predicate still holds.
///
/// `namespace` carries the invariant's namespace for mask enforcement.
/// Part of #2427 Slice 4.
#[doc(hidden)]
pub fn end_invariant_open(invariant_ref: String, namespace: Option<i64>, location: Option<String>) {
    let mut obligation = ProofObligation::new(
        format!("invariant_close_{invariant_ref}"),
        format!("__trust_vc_invariant_close({invariant_ref})"),
        ObligationKind::InvariantClose,
    );
    if let Some(loc) = location {
        obligation = obligation.with_location(loc);
    }
    if let Some(ns) = namespace {
        obligation = obligation.with_invariant_namespace(ns);
    }
    let _ = try_with_session_mut(|s| {
        s.context
            .get_or_insert_with(VerificationContext::new)
            .push_obligation(obligation);
    });
}

/// Translates Rust syntax to SMT using the shared obligation translator.
///
/// Kept as a delegating shim for internal tests that reference
/// `verify_macro::translate_rust_to_smt` via `super::super::`.
#[cfg(test)]
pub(crate) fn translate_rust_to_smt(rust_expr: &str) -> String {
    crate::obligation_collection::translate_rust_to_smt(rust_expr)
}

/// Verifies all collected proof obligations and returns the result.
///
/// This drains the thread-local context, so it can be called multiple times
/// in a test with fresh contexts.
///
/// Semantics:
/// - Empty/uninitialized contexts return `VerifyResult::Error`.
/// - Assumptions-only contexts (no assertions/invariants/assert_by obligations)
///   return `VerifyResult::Error` (`#1859`), not vacuous `Verified`.
#[doc(hidden)]
pub fn verify_collected() -> crate::VerifyResult {
    match crate::context_management::try_take_context() {
        Ok(Some(context)) => context.verify(),
        Ok(None) => crate::VerifyResult::Error {
            message: "No verification context initialized".to_string(),
        },
        Err(crate::context_management::ContextAccessError::VerificationContextBorrowed) => {
            crate::VerifyResult::Error {
                message:
                    "cannot verify collected obligations: verification context is already borrowed"
                        .to_string(),
            }
        }
    }
}

/// Verifies a single quantifier formula inline and returns whether it holds.
///
/// This creates a fresh verification context, adds the quantifier condition
/// as an assertion, verifies it, and returns the result. It does NOT disturb
/// the existing thread-local context — the obligation is still collected
/// there for pipeline-style verification.
///
/// Returns `true` for Verified (formula proven by ay).
/// Returns `false` for Counterexample, Unknown, or Error (conservative — prevents soundness holes).
///
/// The strict policy prevents soundness holes (#1470, #1534) where unparseable
/// or undecidable quantifiers silently pass. The obligation is still collected
/// in the thread-local context for pipeline-level verification.
///
/// This is called by the `forall!`/`exists!` macros in test mode.
#[doc(hidden)]
pub fn verify_quantifier_inline(condition: &str) -> bool {
    use crate::VerifyResult;

    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("quantifier_inline", condition));

    match ctx.verify() {
        VerifyResult::Verified => true,
        // Conservative: anything other than Verified returns false.
        // Error (encoding failure) was previously true (#1534 soundness hole).
        _ => false,
    }
}

/// Verifies trust_vc proof markers in the current module.
///
/// This macro should be called from a test function to verify that all
/// proof obligations in the module are satisfied.
///
/// # Example
///
/// ```ignore
/// #[trust_vc::proof]
/// fn my_lemma() {
///     trust_vc::assert!(true);
/// }
///
/// #[cfg(test)]
/// mod test {
///     use super::*;
///
///     #[test]
///     fn verify_proofs() {
///         trust_vc::verify_markers!();
///     }
/// }
/// ```
///
/// # Panics
///
/// Panics if verification fails, showing the counterexample.
#[macro_export]
macro_rules! verify_markers {
    () => {
        $crate::verify_macro::verify_markers_impl(module_path!(), file!())
    };
}

// verify_markers_impl moved to marker_extraction.rs.
// Re-exported below for backward compatibility.

// verify_proof! macro — must remain here because #[macro_export] macros
// are placed at crate root. The impl function is in decreases_runtime.rs.
#[macro_export]
macro_rules! verify_proof {
    ($func:ident) => {
        $crate::decreases_runtime::verify_proof_impl(stringify!($func), module_path!(), file!())
    };
}

// Include test module — split into domain submodules (#2145)
#[cfg(test)]
#[path = "verify_macro_tests/mod.rs"]
mod verify_macro_tests;
