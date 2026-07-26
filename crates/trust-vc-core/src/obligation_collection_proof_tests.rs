//! Proof coverage tests for obligation_collection.rs
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Covers previously untested production paths: old!() semantics,
//! QuantifierBoundVarGuard RAII, runtime type inference, variable-from-ref
//! type propagation, local tracking, and solver mode parsing.
//!
//! Wired from `obligation_collection/mod.rs` with:
//!   #[cfg(test)]
//!   #[path = "../obligation_collection_proof_tests.rs"]
//!   mod proof_tests;
//!
//! Part of #949.

use super::*;
use crate::context_management::{get_context, with_clean_thread_locals};
use crate::ir::TrustVcType;
use crate::vc::{ObligationKind, SolverMode};

// -- collect_old_value: old!() postcondition pre-state mechanism --

#[test]
fn collect_old_value_declares_old_var_and_adds_equality_assumption() {
    with_clean_thread_locals(|| {
        // Declare "x" as i32 so collect_old_value can look it up
        collect_variable("x".to_string(), "i32".to_string());

        collect_old_value("x".to_string());

        let context = get_context().expect("old value capture should populate context");

        // Should have declared __trust_vc_old_x
        let old_var = context
            .variables
            .iter()
            .find(|v| v.name == "__trust_vc_old_x");
        assert!(
            old_var.is_some(),
            "collect_old_value must declare __trust_vc_old_x in the context"
        );

        // Should have an assumption: __trust_vc_old_x == x
        let old_assumption = context
            .obligations
            .iter()
            .find(|o| o.name == "old_capture_x");
        assert!(
            old_assumption.is_some(),
            "collect_old_value must add an old_capture_x assumption"
        );
        let assumption = old_assumption.unwrap();
        assert_eq!(assumption.kind, ObligationKind::Assume);
        assert!(
            assumption.condition.contains("__trust_vc_old_x")
                && assumption.condition.contains("== x"),
            "old capture assumption should be '__trust_vc_old_x == x', got: {}",
            assumption.condition
        );
    });
}

#[test]
fn collect_old_value_graceful_skip_when_var_undeclared() {
    with_clean_thread_locals(|| {
        // Do NOT declare "y" — collect_old_value should gracefully skip
        collect_old_value("y".to_string());

        let context = get_context();
        // Either no context or no old_capture_y obligation
        let has_old_capture = context
            .map(|c| c.obligations.iter().any(|o| o.name == "old_capture_y"))
            .unwrap_or(false);
        assert!(
            !has_old_capture,
            "collect_old_value must skip when the variable is not declared"
        );
    });
}

// -- QuantifierBoundVarGuard RAII --

#[test]
fn quantifier_bound_var_guard_registers_and_unregisters_on_drop() {
    with_clean_thread_locals(|| {
        // Pre-declare a variable so there's an active session
        collect_variable("dummy".to_string(), "i32".to_string());

        {
            let mut guard = QuantifierBoundVarGuard::new();
            guard.register("qvar_i".to_string(), TrustVcType::Int { width: 32 });
            guard.register("qvar_j".to_string(), TrustVcType::Bool);

            // Inside the scope, both should be resolvable
            let ty_i = lookup_var_type("qvar_i");
            assert_eq!(
                ty_i,
                Some(TrustVcType::Int { width: 32 }),
                "qvar_i should be registered while guard is live"
            );
            let ty_j = lookup_var_type("qvar_j");
            assert_eq!(
                ty_j,
                Some(TrustVcType::Bool),
                "qvar_j should be registered while guard is live"
            );
        }
        // After guard drops, the quantifier-bound vars should be unregistered
        let ty_i_after = lookup_var_type("qvar_i");
        assert_eq!(
            ty_i_after, None,
            "qvar_i should be unregistered after guard drops"
        );
        let ty_j_after = lookup_var_type("qvar_j");
        assert_eq!(
            ty_j_after, None,
            "qvar_j should be unregistered after guard drops"
        );
    });
}

// -- collect_variable_runtime: runtime type inference via Any --

#[test]
fn collect_variable_runtime_infers_type_from_value() {
    with_clean_thread_locals(|| {
        let val_u32: u32 = 42;
        collect_variable_runtime("my_u32", &val_u32);

        let context = get_context().expect("runtime capture should initialize a context");
        let var_ty = context.get_variable_type("my_u32");
        assert!(
            var_ty.is_some(),
            "collect_variable_runtime should declare the variable"
        );
        // std::any::type_name::<u32>() is "u32"; TrustVcType::parse_or_opaque("u32") -> Uint { width: 32 }
        assert_eq!(
            var_ty.cloned(),
            Some(TrustVcType::Uint { width: 32 }),
            "collect_variable_runtime should infer u32 type correctly"
        );
    });
}

#[test]
fn collect_variable_runtime_skips_duplicate() {
    with_clean_thread_locals(|| {
        // Declare "x" first
        collect_variable("x".to_string(), "i32".to_string());

        // Runtime capture for same name should be a no-op
        let val: i32 = 10;
        collect_variable_runtime("x", &val);

        let context = get_context().expect("context should exist");
        let x_vars: Vec<_> = context.variables.iter().filter(|v| v.name == "x").collect();
        assert_eq!(
            x_vars.len(),
            1,
            "collect_variable_runtime should not create duplicate declarations"
        );
    });
}

// -- lookup_var_type: consolidated variable lookup --

#[test]
fn lookup_var_type_checks_local_var_types_first() {
    with_clean_thread_locals(|| {
        // track_local_variable writes to both local_var_types and context.variables
        track_local_variable("tracked_v".to_string(), "u64".to_string());

        let ty = lookup_var_type("tracked_v");
        assert_eq!(
            ty,
            Some(TrustVcType::Uint { width: 64 }),
            "lookup_var_type should find variables registered via track_local_variable"
        );

        // Non-existent variable returns None
        let ty_none = lookup_var_type("nonexistent");
        assert_eq!(
            ty_none, None,
            "lookup_var_type should return None for unknown variables"
        );
    });
}

// -- collect_variable_from_ref: type propagation --

#[test]
fn collect_variable_from_ref_propagates_type() {
    with_clean_thread_locals(|| {
        // Declare reference variable first
        collect_variable("source".to_string(), "i64".to_string());

        // Derive type from reference
        collect_variable_from_ref("dest".to_string(), "source".to_string());

        let context = get_context().expect("context should exist");
        let source_ty = context.get_variable_type("source").cloned();
        let dest_ty = context.get_variable_type("dest").cloned();
        assert_eq!(
            source_ty, dest_ty,
            "collect_variable_from_ref should propagate the source's type to dest"
        );
        assert_eq!(
            dest_ty,
            Some(TrustVcType::Int { width: 64 }),
            "dest should have the same i64 type as source"
        );
    });
}

#[test]
fn collect_variable_from_ref_skips_when_source_undeclared() {
    with_clean_thread_locals(|| {
        // Do NOT declare "missing_source"
        collect_variable_from_ref("dest2".to_string(), "missing_source".to_string());

        // dest2 should not be declared (graceful skip)
        let has_dest = get_context()
            .map(|c| c.variables.iter().any(|v| v.name == "dest2"))
            .unwrap_or(false);
        assert!(
            !has_dest,
            "collect_variable_from_ref should skip when source variable is undeclared"
        );
    });
}

// -- track_local_variable: dual registration --

#[test]
fn track_local_variable_registers_in_both_maps() {
    with_clean_thread_locals(|| {
        track_local_variable("local_x".to_string(), "bool".to_string());

        // Should be in lookup_var_type (which checks local_var_types first)
        let ty = lookup_var_type("local_x");
        assert_eq!(
            ty,
            Some(TrustVcType::Bool),
            "track_local_variable should register in local_var_types"
        );

        // Should also be in context.variables (via collect_variable)
        let context = get_context().expect("tracking should initialize context");
        let in_context = context.variables.iter().any(|v| v.name == "local_x");
        assert!(
            in_context,
            "track_local_variable should also declare in context.variables"
        );
    });
}

// -- parse_solver_mode: exhaustive string mapping --

#[test]
fn parse_solver_mode_maps_known_strings() {
    assert_eq!(
        parse_solver_mode("nonlinear_arith"),
        SolverMode::NonlinearArith
    );
    assert_eq!(parse_solver_mode("bit_vector"), SolverMode::BitVector);
    assert_eq!(parse_solver_mode("compute"), SolverMode::Compute);
    assert_eq!(parse_solver_mode("unknown_mode"), SolverMode::Default);
    assert_eq!(parse_solver_mode(""), SolverMode::Default);
}

#[test]
fn ambient_function_solver_mode_marks_typed_obligations() {
    with_clean_thread_locals(|| {
        let _guard = crate::verify_macro::enter_function_solver_mode_scope(SolverMode::BitVector);

        collect_typed_obligation(
            ObligationKind::Assert,
            "ambient_bv".to_string(),
            "true".to_string(),
            None,
        );

        let context = get_context().expect("ambient obligation should populate context");
        assert_eq!(
            context.obligations[0].solver_mode,
            Some(SolverMode::BitVector)
        );
    });
}

#[test]
fn ambient_function_solver_mode_marks_prebuilt_expr_obligations() {
    with_clean_thread_locals(|| {
        let _guard =
            crate::verify_macro::enter_function_solver_mode_scope(SolverMode::NonlinearArith);

        collect_obligation_expr(
            ObligationKind::Assert,
            "ambient_expr".to_string(),
            "true".to_string(),
            crate::ir_builder::bool_lit(true),
            None,
        );

        let context = get_context().expect("prebuilt obligation should populate context");
        assert_eq!(
            context.obligations[0].solver_mode,
            Some(SolverMode::NonlinearArith)
        );
    });
}

#[test]
fn explicit_solver_mode_overrides_ambient_function_solver_mode() {
    with_clean_thread_locals(|| {
        let _guard =
            crate::verify_macro::enter_function_solver_mode_scope(SolverMode::NonlinearArith);

        collect_solver_mode_obligation(
            ObligationKind::Assert,
            "explicit_bv".to_string(),
            "true".to_string(),
            None,
            "bit_vector",
        );

        let context = get_context().expect("explicit obligation should populate context");
        assert_eq!(
            context.obligations[0].solver_mode,
            Some(SolverMode::BitVector)
        );
    });
}
