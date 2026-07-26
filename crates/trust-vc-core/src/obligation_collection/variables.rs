// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::broadcast_state;
use crate::ir::TrustVcType;
use crate::proof_session::{try_with_session, try_with_session_mut};
use crate::vc::VerificationContext;

/// Looks up a variable's `TrustVcType` from the current verification context.
///
/// Used by proc macro codegen (Phase 5 Step 3b) to resolve variable types
/// at runtime when constructing `TrustVcExpr` trees. Returns the type if the
/// variable is declared, or `None` if not found.
///
/// Consolidated: checks local_var_types and context.variables in a single
/// session borrow. Part of #2481.
pub fn lookup_var_type(name: &str) -> Option<TrustVcType> {
    try_with_session(|s| {
        // First check local_var_types (typed map, more precise)
        s.local_var_types.get(name).cloned().or_else(|| {
            // Fall back to verification context variable declarations
            s.context
                .as_ref()
                .and_then(|context| context.get_variable_type(name).cloned())
        })
    })
    .ok()
    .flatten()
}

/// Collects a variable declaration in the active proof session.
///
/// When in broadcast mode, also records the variable name in BROADCAST_PARAMS
/// so that the resulting BroadcastAssume obligations carry their bound variables.
pub fn collect_variable(name: String, ty: String) {
    // Track broadcast parameters when in broadcast mode (fixes #1618)
    if broadcast_state::is_in_broadcast_mode() {
        broadcast_state::track_broadcast_param(name.clone());
    }

    // Graceful skip on borrow conflict: variable not declared -> encoding
    // may fail, but no crash. Part of #1955.
    let _ = try_with_session_mut(|s| {
        let context = s.context.get_or_insert_with(VerificationContext::new);
        if context.get_variable_type(&name).is_none() {
            context.declare_var_typed(&name, TrustVcType::parse_or_opaque(&ty));
        }
        if is_shared_reference_type_name(&ty) {
            context.mark_erased_shared_ref_var(&name);
        }
    });
}

/// Records that a parameter was annotated with `tracked` in the proof function
/// signature. Tracked params carry proof-mode ownership - Rust's borrow checker
/// enforces single-use, and this metadata enables future mode checking to prevent
/// tracked values from being duplicated in spec expressions. Part of #2427 Slice 3.
pub fn register_tracked_param(name: String) {
    let _ = try_with_session_mut(|s| {
        let context = s.context.get_or_insert_with(VerificationContext::new);
        context.tracked_params.insert(name);
    });
}

/// Registers a prophecy local so later prepared-context lowering can resolve
/// `p.view()` and `p.resolve(...)` through TypeEnv prophecy metadata.
pub fn register_prophecy_local(name: String, inner_ty: String) {
    let _ = try_with_session_mut(|s| {
        let context = s.context.get_or_insert_with(VerificationContext::new);
        context.register_prophecy_binding(&name, TrustVcType::parse_or_opaque(&inner_ty));
    });
}

/// Registers a variable whose type is inferred at runtime from a value reference.
///
/// Used by `assert_by_*` macros which don't have compile-time type information
/// for variables in the condition expression. The macro generates a borrow of
/// each variable, and this function uses `std::any::type_name::<T>()` to
/// determine the type string for the verification context.
///
/// If the variable is already declared in the current context (e.g., from an
/// enclosing `#[proof]` function), this is a no-op to avoid duplicate declarations.
pub fn collect_variable_runtime<T: ?Sized>(name: &str, _val: &T) {
    let type_name = std::any::type_name::<T>().to_string();
    // Intentionally soft: collect_variable_runtime is called from
    // assert_by_* macros which run during proof body execution.
    // A borrow conflict here means the outer scope already holds
    // the RefCell. Not a data loss scenario (#1716).
    let _ = try_with_session_mut(|s| {
        let context = s.context.get_or_insert_with(VerificationContext::new);
        // Skip if already declared (e.g., from enclosing #[proof] function)
        if context.get_variable_type(name).is_none() {
            context.declare_var_typed(name, TrustVcType::parse_or_opaque(&type_name));
        }
        if is_shared_reference_type_name(&type_name) {
            context.mark_erased_shared_ref_var(name);
        }
    });
}

fn is_shared_reference_type_name(ty: &str) -> bool {
    let Some(mut rest) = ty.trim().strip_prefix('&') else {
        return false;
    };
    rest = rest.trim_start();
    if let Some(after_lifetime) = rest.strip_prefix('\'') {
        let lifetime_len = after_lifetime
            .char_indices()
            .find(|(_, ch)| !(*ch == '_' || ch.is_ascii_alphanumeric()))
            .map(|(index, _)| index)
            .unwrap_or(after_lifetime.len());
        rest = after_lifetime[lifetime_len..].trim_start();
    }
    !rest.starts_with('&') && !starts_with_mut_keyword(rest) && !rest.is_empty()
}

fn starts_with_mut_keyword(value: &str) -> bool {
    let Some(rest) = value.strip_prefix("mut") else {
        return false;
    };
    rest.chars()
        .next()
        .is_none_or(|ch| !(ch == '_' || ch.is_ascii_alphanumeric()))
}

/// Registers a variable whose type is inferred from a referenced variable.
///
/// Used when the macro expander encounters `let result = x` inside a proof
/// function. Looks up the type of the referenced variable and registers the
/// new variable with the same type. Panics if the reference has no declared type.
pub fn collect_variable_from_ref(name: String, ref_name: String) {
    // Graceful skip on borrow conflict: variable not declared -> encoding
    // may fail, but no crash. Part of #1955.
    let _ = try_with_session_mut(|s| {
        let context = s.context.get_or_insert_with(VerificationContext::new);
        if let Some(ref_type) = context.get_variable_type(&ref_name).cloned() {
            context.declare_var_typed(&name, ref_type);
        }
        // Graceful skip: if ref_name was not declared (e.g., due to
        // upstream borrow conflict in collect_variable), the new variable
        // is also not declared. The encoder will fail closed at encoding
        // time with a missing-variable error. Part of #1955.
    });
}

/// Registers a counterexample display alias for a solver variable.
///
/// Maps a raw solver variable name (e.g., `__trust_vc_old_x`) to a user-facing
/// display name (e.g., `old(x)`) and visibility flag. The alias takes
/// precedence over the default classifier in `counterexample_names::default_meta`.
/// Part of #2651.
pub fn register_counterexample_display(raw_name: String, display_name: String, visible: bool) {
    let _ = try_with_session_mut(|s| {
        let context = s.context.get_or_insert_with(VerificationContext::new);
        context.register_counterexample_alias(raw_name, display_name, visible);
    });
}

/// Tracks a local variable's type for verification.
///
/// This function is called when local variables are declared within proof functions,
/// allowing the verifier to understand the types of all variables in scope.
/// The string type is parsed to TrustVcType at this boundary (#1863 Slice 4).
pub fn track_local_variable(var_name: String, var_type: String) {
    let trust_vc_ty = TrustVcType::parse_or_opaque(&var_type);

    // Graceful skip on borrow conflict: type info missing -> encoding may
    // fail, but no crash. Part of #1955.
    let _ = try_with_session_mut(|s| {
        s.local_var_types.insert(var_name.clone(), trust_vc_ty);
    });

    // Also collect as a variable declaration for ay (still takes string)
    collect_variable(var_name, var_type);
}
