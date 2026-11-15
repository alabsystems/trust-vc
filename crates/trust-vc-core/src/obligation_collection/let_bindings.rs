// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::collect::{collect_obligation, collect_obligation_expr};
use super::variables::{collect_variable, lookup_var_type, register_counterexample_display};
use crate::ir::TrustVcExpr;
use crate::vc::ObligationKind;
use std::any::Any;

/// Collects a pre-built symbolic let-binding assumption.
pub fn collect_symbolic_let_binding_expr(
    name: String,
    condition_display: String,
    expr: TrustVcExpr,
) {
    collect_obligation_expr(ObligationKind::Assume, name, condition_display, expr, None);
}

/// Collects a pre-built symbolic assume obligation.
pub fn collect_symbolic_assume_expr(name: String, condition_display: String, expr: TrustVcExpr) {
    collect_obligation_expr(ObligationKind::Assume, name, condition_display, expr, None);
}

/// Registers a pre-state snapshot for `old!(var)` in postconditions.
///
/// When `old!(x)` is called, this function:
/// 1. Looks up the type of `x` from local_var_types or context.variables
/// 2. Declares `__trust_vc_old_x` as a ay variable with the same type
/// 3. Adds an assumption `__trust_vc_old_x == x` to capture the current value
///
/// # Panics
///
/// Panics if the variable `var_name` has not been declared in the verification context.
pub fn collect_old_value(var_name: String) {
    let old_var_name = format!("__trust_vc_old_{}", var_name);

    // Consolidated lookup: checks local_var_types first, then context.variables,
    // in a single session borrow. Part of #2481.
    let var_type = match lookup_var_type(&var_name) {
        Some(ty) => ty,
        None => {
            // Graceful skip: if the variable was not declared (e.g., due to
            // upstream borrow conflict in collect_variable), we cannot create
            // the old snapshot. The encoder will fail closed when it encounters
            // the unresolved __trust_vc_old_* reference. Part of #1955.
            return;
        }
    };

    // Declare the old variable with same type (collect_variable still takes string at boundary)
    collect_variable(old_var_name.clone(), var_type.to_type_string());

    // Register display alias so counterexamples show `old(x)` instead of
    // `__trust_vc_old_x`. Part of #2651.
    register_counterexample_display(old_var_name.clone(), format!("old({})", var_name), true);

    // Add assumption: __trust_vc_old_x == x (captures pre-state)
    collect_obligation(
        ObligationKind::Assume,
        format!("old_capture_{}", var_name),
        format!("{} == {}", old_var_name, var_name),
        None,
    );
}

/// Registers a pre-state snapshot for `old!(*var)` (deref capture) in postconditions.
///
/// Like `collect_old_value` but registers the display alias as `old(*var_name)`
/// to distinguish value captures from deref captures in counterexamples.
/// Part of #2651.
pub fn collect_old_value_deref(var_name: String) {
    let old_var_name = format!("__trust_vc_old_{}", var_name);

    let var_type = match lookup_var_type(&var_name) {
        Some(ty) => ty,
        None => return,
    };

    collect_variable(old_var_name.clone(), var_type.to_type_string());

    register_counterexample_display(old_var_name.clone(), format!("old(*{})", var_name), true);

    collect_obligation(
        ObligationKind::Assume,
        format!("old_capture_{}", var_name),
        format!("{} == {}", old_var_name, var_name),
        None,
    );
}

/// Registers a snapshot for `final!(var)` in postconditions — the symmetric
/// twin of [`collect_old_value`] for the new-mut-ref/prophecy core.
///
/// New-mut-ref Phase 0 (`docs/archive/design-new-mut-ref.md`): this exists only so the
/// `final!()` macro-emitted tokens reference a real symbol. It mirrors the
/// `old!()` snapshot mechanics (declare `__trust_vc_final_var`, alias display,
/// assume equality with the current value). Phase 0 wires no caller that emits
/// these calls, so it introduces no verification behavior. Phases 1+ replace
/// the assumed equality with a fresh prophecy constant resolved at exit.
///
/// # Panics
///
/// Does not panic: gracefully skips (like `collect_old_value`) when the
/// variable has not been declared in the verification context.
pub fn collect_final_value(var_name: String) {
    let final_var_name = format!("__trust_vc_final_{}", var_name);

    let var_type = match lookup_var_type(&var_name) {
        Some(ty) => ty,
        None => return,
    };

    collect_variable(final_var_name.clone(), var_type.to_type_string());

    register_counterexample_display(final_var_name.clone(), format!("final({})", var_name), true);

    collect_obligation(
        ObligationKind::Assume,
        format!("final_capture_{}", var_name),
        format!("{} == {}", final_var_name, var_name),
        None,
    );
}

/// Registers a snapshot for `final!(*var)` (deref capture) in postconditions —
/// the symmetric twin of [`collect_old_value_deref`].
///
/// Like [`collect_final_value`] but registers the display alias as
/// `final(*var_name)` to distinguish value captures from deref captures in
/// counterexamples. New-mut-ref Phase 0: pure plumbing, no verification
/// behavior wired in.
pub fn collect_final_value_deref(var_name: String) {
    let final_var_name = format!("__trust_vc_final_{}", var_name);

    let var_type = match lookup_var_type(&var_name) {
        Some(ty) => ty,
        None => return,
    };

    collect_variable(final_var_name.clone(), var_type.to_type_string());

    register_counterexample_display(
        final_var_name.clone(),
        format!("final(*{})", var_name),
        true,
    );

    collect_obligation(
        ObligationKind::Assume,
        format!("final_capture_{}", var_name),
        format!("{} == {}", final_var_name, var_name),
        None,
    );
}

/// Collects a let-binding constraint as an assumption in the verification context.
///
/// When a proof function contains `let y: i32 = 5 * 5;`, the macro calls
/// `collect_variable("y", "i32")` then this function to add `y == 5 * 5`.
/// Without this assumption, the solver treats `y` as unconstrained.
/// Fixes #1556.
pub fn collect_let_binding(var_name: String, init_expr: String) {
    let _ = crate::proof_session::try_with_session_mut(|session| {
        session
            .local_let_bindings
            .insert(var_name.clone(), init_expr.clone());
    });
    collect_obligation(
        ObligationKind::Assume,
        format!("let_binding_{}", var_name),
        format!("{} == {}", var_name, init_expr),
        None,
    );
}

/// Adds runtime let-binding value as assumption. i64 covers i8..i64, u8..u32.
/// For larger types, use the i128/u128 variants. Fixes #1556.
pub fn collect_let_binding_runtime_value(var_name: String, value: i64) {
    collect_obligation(
        ObligationKind::Assume,
        format!("let_binding_runtime_{}", var_name),
        format!("{} == {}", var_name, value),
        None,
    );
}

/// Like `collect_let_binding_runtime_value` but for i128 (u64/i128/u128/usize).
pub fn collect_let_binding_runtime_value_i128(var_name: String, value: i128) {
    collect_obligation(
        ObligationKind::Assume,
        format!("let_binding_runtime_{}", var_name),
        format!("{} == {}", var_name, value),
        None,
    );
}

/// Like `collect_let_binding_runtime_value` but for u128 (avoids i128 wrapping).
pub fn collect_let_binding_runtime_value_u128(var_name: String, value: u128) {
    collect_obligation(
        ObligationKind::Assume,
        format!("let_binding_runtime_{}", var_name),
        format!("{} == {}", var_name, value),
        None,
    );
}

/// Adds a runtime let-binding assumption by downcasting a referenced value.
///
/// This is the dynamic counterpart to `emit_runtime_value_capture` in
/// `local_vars.rs`: it supports the same bool/integer surface but works when
/// the proc-macro expansion only has a value reference instead of a type string.
/// Unsupported runtime types are ignored so the caller can stay fail-closed.
pub fn collect_let_binding_runtime_value_from_ref<T: 'static>(var_name: &str, value: &T) {
    let any = value as &dyn Any;

    if let Some(value) = any.downcast_ref::<i8>() {
        collect_let_binding_runtime_value(var_name.to_string(), i64::from(*value));
        return;
    }
    if let Some(value) = any.downcast_ref::<i16>() {
        collect_let_binding_runtime_value(var_name.to_string(), i64::from(*value));
        return;
    }
    if let Some(value) = any.downcast_ref::<i32>() {
        collect_let_binding_runtime_value(var_name.to_string(), i64::from(*value));
        return;
    }
    if let Some(value) = any.downcast_ref::<i64>() {
        collect_let_binding_runtime_value(var_name.to_string(), *value);
        return;
    }
    if let Some(value) = any.downcast_ref::<u8>() {
        collect_let_binding_runtime_value(var_name.to_string(), i64::from(*value));
        return;
    }
    if let Some(value) = any.downcast_ref::<u16>() {
        collect_let_binding_runtime_value(var_name.to_string(), i64::from(*value));
        return;
    }
    if let Some(value) = any.downcast_ref::<u32>() {
        collect_let_binding_runtime_value(var_name.to_string(), i64::from(*value));
        return;
    }
    if let Some(value) = any.downcast_ref::<u64>() {
        collect_let_binding_runtime_value_i128(var_name.to_string(), i128::from(*value));
        return;
    }
    if let Some(value) = any.downcast_ref::<usize>() {
        collect_let_binding_runtime_value_i128(var_name.to_string(), *value as i128);
        return;
    }
    if let Some(value) = any.downcast_ref::<isize>() {
        collect_let_binding_runtime_value_i128(var_name.to_string(), *value as i128);
        return;
    }
    if let Some(value) = any.downcast_ref::<i128>() {
        collect_let_binding_runtime_value_i128(var_name.to_string(), *value);
        return;
    }
    if let Some(value) = any.downcast_ref::<u128>() {
        collect_let_binding_runtime_value_u128(var_name.to_string(), *value);
        return;
    }
    if let Some(value) = any.downcast_ref::<bool>() {
        // Use string "true"/"false" to avoid Bool vs Int sort mismatch. Fixes #2558.
        collect_let_binding(
            var_name.to_string(),
            if *value { "true" } else { "false" }.to_string(),
        );
    }
}
