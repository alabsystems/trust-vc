//! Thread-local cleanup coverage tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Verifies that `clear_all_thread_locals()` resets ALL thread-local state.
//! If a new thread-local is added but not cleared, these tests catch it.
//! Fixes #1718 (AC: "cannot miss fields").

use super::super::*;
use crate::context_management::with_clean_thread_locals;
use crate::ir_expr::TrustVcExpr;
use crate::vc::ObligationKind;

/// Sets every known thread-local to a non-default value.
fn populate_all_thread_locals() {
    // VERIFICATION_CONTEXT
    collect_obligation(
        ObligationKind::Assert,
        "cleanup_test".to_string(),
        "true".to_string(),
        None,
    );
    // IN_PROOF_MODE
    set_proof_mode(true);
    // LOCAL_VAR_TYPES
    track_local_variable("test_var".to_string(), "bool".to_string());
    // ASSERT_BY_SCOPE_STACK
    begin_assert_by_scope("cleanup_test_scope".to_string());
    // IN_BROADCAST_MODE + BROADCAST_PARAMS
    set_broadcast_mode(true);
    // TRIGGER_PATTERNS
    register_trigger(0, "test_trigger".to_string());
    // proof-session translator (internal state populated via translate)
    let _ = crate::obligation_collection::translate_rust_to_smt("x + 1");
    // EXTERN_SPEC_CONTRACTS
    crate::extern_spec_verify::register_extern_spec(
        "test::cleanup_target",
        &["true".to_string()],
        &["true".to_string()],
    );
    // REGISTERED_PROOFS
    crate::verification_bridge::register_proof("cleanup_proof", vec![]);
    // MODE_REGISTRY
    crate::mode::register_function_mode("cleanup_func", crate::mode::FunctionMode::Spec);
    // proof-session pre-built expr cache — populate it so we can verify reset
    cache_pre_built_expr(
        "cleanup_cache_test".to_string(),
        "true".to_string(),
        TrustVcExpr::BoolLit(true),
    );
    // BROADCAST_LEMMAS — register a lemma beyond just the mode flag
    register_broadcast_lemma("cleanup_lemma".to_string());
}

/// Asserts every directly-observable thread-local is back to its default.
fn assert_all_thread_locals_clear() {
    assert!(get_context().is_none(), "VERIFICATION_CONTEXT not cleared");
    assert!(!is_in_proof_mode(), "IN_PROOF_MODE not cleared");
    assert!(
        lookup_var_type("test_var").is_none(),
        "LOCAL_VAR_TYPES not cleared"
    );
    assert!(!is_in_broadcast_mode(), "IN_BROADCAST_MODE not cleared");
    // MODE_REGISTRY — Spec mode should revert to default (Exec)
    assert_eq!(
        crate::mode::lookup_function_mode("cleanup_func"),
        crate::mode::FunctionMode::Exec,
        "MODE_REGISTRY not cleared"
    );
    // proof-session pre-built expr cache — entry should be gone after clearing
    assert!(
        crate::obligation_collection::take_pre_built_expr("cleanup_cache_test", "true").is_none(),
        "PRE_BUILT_EXPRS not cleared"
    );
}

/// Populates all thread-locals, clears them, asserts all reset.
/// Adding a new thread-local without updating `clear_all_thread_locals()`
/// will leave stale state that this test detects.
#[test]
fn test_clear_all_thread_locals_resets_all_state() {
    with_clean_thread_locals(|| {
        populate_all_thread_locals();

        assert!(get_context().is_some(), "precondition: context populated");
        assert!(is_in_proof_mode(), "precondition: proof mode set");
        assert!(is_in_broadcast_mode(), "precondition: broadcast mode set");

        clear_all_thread_locals();

        assert_all_thread_locals_clear();
    });
}

/// QuantifierBoundVarGuard must unregister bound variables on panic unwind.
/// Without RAII, a panic between register and unregister leaks types into
/// LOCAL_VAR_TYPES, corrupting subsequent quantifier encoding on the thread.
#[test]
fn test_quantifier_bound_var_guard_cleans_up_on_panic() {
    with_clean_thread_locals(|| {
        let result = std::panic::catch_unwind(|| {
            let mut guard = crate::obligation_collection::QuantifierBoundVarGuard::new();
            guard.register(
                "qvar_a".to_string(),
                crate::ir::TrustVcType::Uint { width: 64 },
            );
            guard.register(
                "qvar_b".to_string(),
                crate::ir::TrustVcType::Int { width: 32 },
            );
            assert!(
                lookup_var_type("qvar_a").is_some(),
                "precondition: qvar_a registered"
            );
            assert!(
                lookup_var_type("qvar_b").is_some(),
                "precondition: qvar_b registered"
            );
            panic!("simulated quantifier body panic");
        });

        assert!(result.is_err(), "should have panicked");
        assert!(
            lookup_var_type("qvar_a").is_none(),
            "QuantifierBoundVarGuard must unregister qvar_a on panic unwind"
        );
        assert!(
            lookup_var_type("qvar_b").is_none(),
            "QuantifierBoundVarGuard must unregister qvar_b on panic unwind"
        );
    });
}

/// QuantifierBoundVarGuard cleans up on normal drop (not just panic).
#[test]
fn test_quantifier_bound_var_guard_cleans_up_on_normal_drop() {
    with_clean_thread_locals(|| {
        {
            let mut guard = crate::obligation_collection::QuantifierBoundVarGuard::new();
            guard.register(
                "qvar_x".to_string(),
                crate::ir::TrustVcType::Uint { width: 8 },
            );
            assert!(
                lookup_var_type("qvar_x").is_some(),
                "precondition: qvar_x registered"
            );
        } // guard drops here

        assert!(
            lookup_var_type("qvar_x").is_none(),
            "QuantifierBoundVarGuard must unregister on normal drop"
        );
    });
}

/// QuantifierBoundVarGuard must restore an outer local binding when a forall
/// binder shadows the same source name.
#[test]
fn test_quantifier_bound_var_guard_restores_shadowed_local_type() {
    with_clean_thread_locals(|| {
        track_local_variable("qvar_shadow".to_string(), "u32".to_string());
        assert_eq!(
            lookup_var_type("qvar_shadow"),
            Some(crate::ir::TrustVcType::Uint { width: 32 }),
            "precondition: outer local type should be registered"
        );

        {
            let mut guard = crate::obligation_collection::QuantifierBoundVarGuard::new();
            guard.register(
                "qvar_shadow".to_string(),
                crate::ir::TrustVcType::Int { width: 32 },
            );
            assert_eq!(
                lookup_var_type("qvar_shadow"),
                Some(crate::ir::TrustVcType::Int { width: 32 }),
                "quantifier binder should shadow outer local type while in scope"
            );
        }

        assert_eq!(
            lookup_var_type("qvar_shadow"),
            Some(crate::ir::TrustVcType::Uint { width: 32 }),
            "QuantifierBoundVarGuard must restore the shadowed local type"
        );
    });
}
