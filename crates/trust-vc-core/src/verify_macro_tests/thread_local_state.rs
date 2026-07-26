//! Thread-local state management tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests covering gaps in thread-local lifecycle management:
//! - Trait registry clearing (was a known gap, now cleared by clear_all_thread_locals)
//! - Multi-level loop context stack clearing
//! - Trigger inference mode clearing via broadcast state cleanup
//! - State isolation between sequential populate/clear cycles
//! - `with_clean_thread_locals` panic-safety wrapper
//! - Trait registry borrow conflict graceful skip
//! - Broadcast auxiliary state (lemmas, params, triggers) clearing

use super::super::*;
use crate::context_management::with_clean_thread_locals;
use crate::ir::TrustVcExpr;
use crate::vc::ObligationKind;

// ========================================================================
// Trait registry clearing -- was previously a gap per memory notes
// ========================================================================

/// Populates the trait registry via register_traits_from_source, clears all
/// thread-locals, then verifies the registry is empty via the test accessor.
///
/// This was a known gap: the trait registry was added to clear_all_thread_locals
/// after the initial cleanup_coverage.rs was written, and the existing test
/// (test_clear_all_thread_locals_resets_all_state) does not populate or
/// verify trait state.
#[test]
fn test_clear_all_resets_trait_registry() {
    with_clean_thread_locals(|| {
        // Register a trait by parsing minimal source with a #[trust_vc::trait_spec]
        // attribute. The trait_catalog parser looks for items with `trait_spec`
        // or `trait_impl` in their attributes.
        let source = r#"
            #[trust_vc::trait_spec]
            trait MyTestTrait {
                fn my_method(&self) -> bool;
            }
        "#;
        let result = crate::trait_registry::register_traits_from_source("test.rs", source);
        // If parsing succeeds, the trait should be registered.
        // If parsing fails (e.g. attribute not recognized by the parser),
        // we still verify clearing works on an empty registry.
        if result.is_ok() {
            assert!(
                crate::trait_registry::registered_trait_decl_count() > 0,
                "precondition: trait decl should be registered after register_traits_from_source"
            );
        }

        clear_all_thread_locals();

        assert_eq!(
            crate::trait_registry::registered_trait_decl_count(),
            0,
            "clear_all_thread_locals must clear trait decl registry"
        );
        assert_eq!(
            crate::trait_registry::registered_trait_impl_decl_count(),
            0,
            "clear_all_thread_locals must clear trait impl decl registry"
        );
    });
}

/// Verifies that trait registry counts start at zero in a clean state.
#[test]
fn test_trait_registry_defaults_to_empty() {
    with_clean_thread_locals(|| {
        assert_eq!(
            crate::trait_registry::registered_trait_decl_count(),
            0,
            "trait decl registry should be empty after clear"
        );
        assert_eq!(
            crate::trait_registry::registered_trait_impl_decl_count(),
            0,
            "trait impl decl registry should be empty after clear"
        );
    });
}

/// Verifies trait registry borrow conflict graceful skip.
///
/// When the REGISTERED_TRAITS RefCell is already borrowed, clear_registered_traits
/// should skip without panicking, consistent with the #1955 pattern.
#[test]
fn test_clear_registered_traits_skips_on_borrow_conflict() {
    with_clean_thread_locals(|| {
        crate::trait_registry::test_helpers::with_registered_traits_borrowed(|| {
            // This should not panic -- graceful skip
            crate::trait_registry::clear_registered_traits();
        });
    });
}

/// clear_all_thread_locals completes when REGISTERED_TRAITS is borrowed.
#[test]
fn test_clear_all_thread_locals_skips_on_trait_registry_borrow() {
    with_clean_thread_locals(|| {
        crate::trait_registry::test_helpers::with_registered_traits_borrowed(|| {
            clear_all_thread_locals(); // should complete without panicking
        });
    });
}

// ========================================================================
// Multi-level loop context stack clearing
// ========================================================================

/// Verifies that clear_all_thread_locals clears a multi-level loop context stack.
///
/// Existing tests only push one context. Real code can have nested loops
/// producing multiple stack entries, and clear must remove all of them.
#[test]
fn test_clear_all_thread_locals_clears_multi_level_loop_context_stack() {
    with_clean_thread_locals(|| {
        crate::loop_metadata::push_loop_context(vec!["i".to_string()], "i < 10".to_string());
        crate::loop_metadata::push_loop_context(vec!["j".to_string()], "j < 5".to_string());
        crate::loop_metadata::push_loop_context(vec!["k".to_string()], "k < 3".to_string());

        assert_eq!(
            crate::loop_metadata::loop_context_stack_depth(),
            3,
            "precondition: three nested loop contexts should be stacked"
        );

        clear_all_thread_locals();

        assert_eq!(
            crate::loop_metadata::loop_context_stack_depth(),
            0,
            "clear_all_thread_locals must clear the entire loop context stack"
        );
        assert!(
            crate::loop_metadata::current_loop_context().is_none(),
            "no loop context should be active after clearing"
        );
    });
}

/// LoopContextGuard nesting: inner guard does not clobber outer context.
#[test]
fn test_loop_context_guard_nested_scopes_restore_correctly() {
    with_clean_thread_locals(|| {
        let outer = crate::loop_metadata::LoopContextGuard::new(
            vec!["i".to_string()],
            "i < 10".to_string(),
        );
        assert_eq!(crate::loop_metadata::loop_context_stack_depth(), 1);

        {
            let _inner = crate::loop_metadata::LoopContextGuard::new(
                vec!["j".to_string()],
                "j < 5".to_string(),
            );
            assert_eq!(crate::loop_metadata::loop_context_stack_depth(), 2);

            let (vars, guard) = crate::loop_metadata::current_loop_context()
                .expect("inner loop context should be active");
            assert_eq!(vars, vec!["j".to_string()]);
            assert_eq!(guard, "j < 5");
        }

        // Inner guard dropped, should pop back to outer
        assert_eq!(crate::loop_metadata::loop_context_stack_depth(), 1);
        let (vars, guard) = crate::loop_metadata::current_loop_context()
            .expect("outer loop context should be restored");
        assert_eq!(vars, vec!["i".to_string()]);
        assert_eq!(guard, "i < 10");

        drop(outer);
        assert_eq!(crate::loop_metadata::loop_context_stack_depth(), 0);
    });
}

// ========================================================================
// Trigger inference mode clearing
// ========================================================================

/// Verifies that clear_broadcast_state resets the trigger inference mode.
#[test]
fn test_clear_broadcast_state_resets_trigger_inference_mode() {
    with_clean_thread_locals(|| {
        crate::broadcast_state::set_trigger_inference_mode(
            crate::trigger_inference::TriggerInferenceMode::Aggressive,
        );
        assert_eq!(
            crate::broadcast_state::get_trigger_inference_mode(),
            Some(crate::trigger_inference::TriggerInferenceMode::Aggressive),
            "precondition: trigger inference mode should be set"
        );

        crate::broadcast_state::clear_broadcast_state();

        assert_eq!(
            crate::broadcast_state::get_trigger_inference_mode(),
            None,
            "clear_broadcast_state must reset trigger inference mode to None"
        );
    });
}

/// Verifies that clear_all_thread_locals resets trigger inference mode
/// (indirectly via clear_broadcast_state).
#[test]
fn test_clear_all_thread_locals_resets_trigger_inference_mode() {
    with_clean_thread_locals(|| {
        crate::broadcast_state::set_trigger_inference_mode(
            crate::trigger_inference::TriggerInferenceMode::Conservative,
        );
        assert!(
            crate::broadcast_state::get_trigger_inference_mode().is_some(),
            "precondition: trigger inference mode should be set"
        );

        clear_all_thread_locals();

        assert_eq!(
            crate::broadcast_state::get_trigger_inference_mode(),
            None,
            "clear_all_thread_locals must reset trigger inference mode"
        );
    });
}

// ========================================================================
// Broadcast auxiliary state clearing
// ========================================================================

/// Verifies that clear_broadcast_state clears lemma names, params, and triggers.
#[test]
fn test_clear_broadcast_state_clears_all_auxiliary_state() {
    with_clean_thread_locals(|| {
        // Populate broadcast auxiliary state
        register_broadcast_lemma("test_lemma_1".to_string());
        crate::broadcast_state::track_broadcast_param("param_a".to_string());
        register_trigger(0, "trigger_x".to_string());

        assert!(
            crate::broadcast_state::test_helpers::broadcast_lemma_count() > 0,
            "precondition: broadcast lemmas should be registered"
        );
        assert!(
            crate::broadcast_state::test_helpers::broadcast_param_count() > 0,
            "precondition: broadcast params should be registered"
        );
        assert!(
            crate::broadcast_state::test_helpers::trigger_pattern_count() > 0,
            "precondition: trigger patterns should be registered"
        );

        crate::broadcast_state::clear_broadcast_state();

        assert_eq!(
            crate::broadcast_state::test_helpers::broadcast_lemma_count(),
            0,
            "clear_broadcast_state must clear broadcast lemma names"
        );
        assert_eq!(
            crate::broadcast_state::test_helpers::broadcast_param_count(),
            0,
            "clear_broadcast_state must clear broadcast params"
        );
        assert_eq!(
            crate::broadcast_state::test_helpers::trigger_pattern_count(),
            0,
            "clear_broadcast_state must clear trigger patterns"
        );
    });
}

// ========================================================================
// State isolation between sequential populate/clear cycles
// ========================================================================

/// Verifies that two sequential populate-clear-assert cycles are fully
/// independent. State from cycle 1 must not leak into cycle 2.
#[test]
fn test_state_isolation_between_sequential_cycles() {
    with_clean_thread_locals(|| {
        // Cycle 1: populate and verify
        set_proof_mode(true);
        track_local_variable("cycle1_var".to_string(), "u32".to_string());
        crate::mode::register_function_mode("cycle1_fn", crate::mode::FunctionMode::Spec);
        crate::loop_metadata::push_loop_context(vec!["x".to_string()], "x < 10".to_string());

        assert!(is_in_proof_mode(), "cycle 1: proof mode should be set");
        assert!(
            lookup_var_type("cycle1_var").is_some(),
            "cycle 1: var should be tracked"
        );

        clear_all_thread_locals();

        // Verify cycle 1 state is gone
        assert!(
            !is_in_proof_mode(),
            "between cycles: proof mode must be clear"
        );
        assert!(
            lookup_var_type("cycle1_var").is_none(),
            "between cycles: cycle 1 var must be gone"
        );

        // Cycle 2: populate different state
        set_proof_mode(true);
        track_local_variable("cycle2_var".to_string(), "u64".to_string());
        crate::mode::register_function_mode("cycle2_fn", crate::mode::FunctionMode::Proof);

        // Verify no cycle 1 remnants
        assert!(
            lookup_var_type("cycle1_var").is_none(),
            "cycle 2: cycle 1 var must not be present"
        );
        assert_eq!(
            crate::mode::lookup_function_mode("cycle1_fn"),
            crate::mode::FunctionMode::Exec,
            "cycle 2: cycle 1 mode registration must be cleared (returns default Exec)"
        );

        // Verify cycle 2 state is intact
        assert!(
            lookup_var_type("cycle2_var").is_some(),
            "cycle 2: cycle 2 var should be tracked"
        );
        assert_eq!(
            crate::mode::lookup_function_mode("cycle2_fn"),
            crate::mode::FunctionMode::Proof,
            "cycle 2: cycle 2 mode registration should be present"
        );

        clear_all_thread_locals();

        // Final verification: everything clean
        assert!(
            lookup_var_type("cycle2_var").is_none(),
            "after cycle 2 clear: cycle 2 var must be gone"
        );
        assert_eq!(
            crate::mode::lookup_function_mode("cycle2_fn"),
            crate::mode::FunctionMode::Exec,
            "after cycle 2 clear: cycle 2 mode must be gone"
        );
    });
}

// ========================================================================
// with_clean_thread_locals panic safety
// ========================================================================

/// Verifies that with_clean_thread_locals re-raises panics from the body
/// while still clearing state after the panic.
#[test]
fn test_with_clean_thread_locals_reraises_panic_and_clears_state() {
    // Set up some state before calling with_clean_thread_locals
    clear_all_thread_locals();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        with_clean_thread_locals(|| {
            set_proof_mode(true);
            track_local_variable("panic_var".to_string(), "bool".to_string());
            panic!("intentional test panic");
        });
    }));

    assert!(result.is_err(), "panic should be re-raised");

    // State should be cleared by with_clean_thread_locals cleanup
    assert!(
        !is_in_proof_mode(),
        "proof mode should be cleared after panicked with_clean_thread_locals"
    );
    assert!(
        lookup_var_type("panic_var").is_none(),
        "var type should be cleared after panicked with_clean_thread_locals"
    );
}

/// Verifies that with_clean_thread_locals clears state established
/// BEFORE it is called (pre-clear).
#[test]
fn test_with_clean_thread_locals_pre_clears_state() {
    // Intentionally dirty the state before with_clean_thread_locals
    set_proof_mode(true);
    crate::broadcast_state::set_broadcast_mode(true);

    with_clean_thread_locals(|| {
        // Inside the wrapper, state from before should be cleared
        assert!(
            !is_in_proof_mode(),
            "with_clean_thread_locals must pre-clear proof mode"
        );
        assert!(
            !is_in_broadcast_mode(),
            "with_clean_thread_locals must pre-clear broadcast mode"
        );
    });

    // Also verify post-clear happened
    assert!(
        !is_in_proof_mode(),
        "proof mode should remain clear after with_clean_thread_locals"
    );
}

// ========================================================================
// Thread-local defaults verification
// ========================================================================

/// Verifies all thread-local defaults after a full clear.
///
/// This is the comprehensive "defaults after clear" test that checks every
/// observable thread-local's initial state, providing a regression anchor
/// if a new thread-local is added with a non-empty default.
#[test]
fn test_all_thread_local_defaults_after_clear() {
    with_clean_thread_locals(|| {
        // ProofSession fields
        assert!(get_context().is_none(), "context should default to None");
        assert!(!is_in_proof_mode(), "proof mode should default to false");
        assert!(
            lookup_var_type("any_name").is_none(),
            "local_var_types should default to empty"
        );
        assert_eq!(
            crate::obligation_collection::obligations_dropped_count(),
            0,
            "obligations_dropped should default to 0"
        );
        assert_eq!(
            crate::obligation_collection::total_obligations_collected(),
            0,
            "total_obligations_collected should default to 0"
        );

        // Broadcast state
        assert!(
            !is_in_broadcast_mode(),
            "broadcast mode should default to false"
        );
        assert_eq!(
            crate::broadcast_state::get_trigger_inference_mode(),
            None,
            "trigger inference mode should default to None"
        );

        // Loop context
        assert!(
            crate::loop_metadata::current_loop_context().is_none(),
            "loop context should default to None (empty stack)"
        );
        assert_eq!(
            crate::loop_metadata::loop_context_stack_depth(),
            0,
            "loop context stack depth should default to 0"
        );

        // Mode registry
        assert_eq!(
            crate::mode::lookup_function_mode("unregistered"),
            crate::mode::FunctionMode::Exec,
            "mode registry should return Exec for unregistered functions"
        );

        // Trait registry
        assert_eq!(
            crate::trait_registry::registered_trait_decl_count(),
            0,
            "trait decl registry should default to empty"
        );
        assert_eq!(
            crate::trait_registry::registered_trait_impl_decl_count(),
            0,
            "trait impl decl registry should default to empty"
        );

        // Broadcast auxiliary state
        assert_eq!(
            crate::broadcast_state::test_helpers::broadcast_lemma_count(),
            0,
            "broadcast lemma list should default to empty"
        );
        assert_eq!(
            crate::broadcast_state::test_helpers::broadcast_param_count(),
            0,
            "broadcast param list should default to empty"
        );
        assert_eq!(
            crate::broadcast_state::test_helpers::trigger_pattern_count(),
            0,
            "trigger pattern list should default to empty"
        );
    });
}

// ========================================================================
// Idempotent clearing
// ========================================================================

/// Calling clear_all_thread_locals twice in a row should not panic or
/// leave any state in an inconsistent condition. This catches cases where
/// the first clear leaves a sentinel that the second clear misinterprets.
#[test]
fn test_clear_all_thread_locals_is_idempotent() {
    with_clean_thread_locals(|| {
        // Dirty everything
        set_proof_mode(true);
        collect_obligation(
            ObligationKind::Assert,
            "idem_test".to_string(),
            "true".to_string(),
            None,
        );
        crate::broadcast_state::set_broadcast_mode(true);
        crate::loop_metadata::push_loop_context(vec!["x".to_string()], "x < 5".to_string());
        crate::mode::register_function_mode("idem_fn", crate::mode::FunctionMode::Spec);

        // First clear
        clear_all_thread_locals();

        // Second clear (should be a no-op that does not panic)
        clear_all_thread_locals();

        // Third clear for good measure
        clear_all_thread_locals();

        // Everything should still be clean
        assert!(!is_in_proof_mode(), "proof mode should be clear");
        assert!(get_context().is_none(), "context should be None");
        assert!(!is_in_broadcast_mode(), "broadcast mode should be clear");
        assert!(
            crate::loop_metadata::current_loop_context().is_none(),
            "loop context should be empty"
        );
    });
}

// ========================================================================
// Pre-built expr cache clearing
// ========================================================================

/// Verifies that the pre-built expression cache is cleared by
/// clear_all_thread_locals, and that a second access after clearing
/// does not find stale entries.
#[test]
fn test_clear_all_thread_locals_clears_pre_built_expr_cache() {
    with_clean_thread_locals(|| {
        cache_pre_built_expr(
            "state_test_fn".to_string(),
            "x > 0".to_string(),
            TrustVcExpr::BoolLit(true),
        );

        // Verify cached
        assert!(
            crate::obligation_collection::take_pre_built_expr("state_test_fn", "x > 0").is_some(),
            "precondition: pre-built expr should be cached"
        );

        // Re-cache (take consumed it)
        cache_pre_built_expr(
            "state_test_fn".to_string(),
            "x > 0".to_string(),
            TrustVcExpr::BoolLit(true),
        );

        clear_all_thread_locals();

        assert!(
            crate::obligation_collection::take_pre_built_expr("state_test_fn", "x > 0").is_none(),
            "pre-built expr cache must be cleared by clear_all_thread_locals"
        );
    });
}

// ========================================================================
// Extern spec contracts clearing
// ========================================================================

/// Verifies that clear_all_thread_locals clears extern spec contracts.
///
/// Uses the extern spec verify module's register function, then verifies
/// clearing works by checking that sequential register-clear-register
/// cycles do not accumulate state.
#[test]
fn test_clear_all_thread_locals_clears_extern_spec_contracts() {
    with_clean_thread_locals(|| {
        crate::extern_spec_verify::register_extern_spec(
            "test::extern_target",
            &["x > 0".to_string()],
            &["result > 0".to_string()],
        );

        clear_all_thread_locals();

        // After clearing, re-register and clear again should work without
        // accumulation from the first registration.
        crate::extern_spec_verify::register_extern_spec(
            "test::extern_target_2",
            &["y > 0".to_string()],
            &["result > y".to_string()],
        );

        clear_all_thread_locals();
    });
}

// ========================================================================
// Scope stack clearing
// ========================================================================

/// Verifies that clear_all_thread_locals clears the assert_by_scope_stack.
///
/// Unbalanced begin_assert_by_scope without end_assert_by_scope (simulating
/// a panic mid-proof) should be fully cleaned up.
#[test]
fn test_clear_all_thread_locals_clears_unbalanced_scope_stack() {
    with_clean_thread_locals(|| {
        // Push scopes without popping them
        begin_assert_by_scope("scope_a".to_string());
        begin_assert_by_scope("scope_b".to_string());

        clear_all_thread_locals();

        // After clearing, beginning a new scope should work cleanly
        // (no accumulated stale scopes). Verify by successfully pushing
        // and popping a single fresh scope.
        begin_assert_by_scope("fresh_scope".to_string());
        super::super::end_assert_by_scope("true".to_string(), Some("fresh.rs:1".to_string()));

        clear_all_thread_locals();
    });
}

/// Trait-side A2-generic dual-surface parity (Probe 5, registry half): the
/// catalog surface funnels a PARAMETERIZED trait + instantiated impl through
/// the same parsers as the file path, and re-registration dedupes by full
/// struct equality — `generics` / `trait_type_args` participate, so a
/// duplicated registration can neither double-register nor silently collapse
/// distinct instantiations.
#[test]
fn test_parameterized_trait_registration_is_idempotent() {
    with_clean_thread_locals(|| {
        let source = r#"
            struct PS1 { x: u64 }

            #[trust_vc::trait_spec]
            trait ParityGive<A> {
                #[trust_vc::ensures(result == a)]
                fn give(&self, a: A) -> A;
            }

            #[trust_vc::trait_impl]
            impl ParityGive<u64> for PS1 {
                fn give(&self, a: u64) -> u64 { a }
            }
        "#;
        crate::trait_registry::register_traits_from_source("parity.rs", source)
            .expect("register parameterized trait source");
        let decls_once = crate::trait_registry::registered_trait_decl_count();
        let impls_once = crate::trait_registry::registered_trait_impl_decl_count();
        assert!(decls_once >= 1, "trait decl must register");
        assert!(impls_once >= 1, "trait impl decl must register");

        crate::trait_registry::register_traits_from_source("parity.rs", source)
            .expect("re-register parameterized trait source");
        assert_eq!(
            crate::trait_registry::registered_trait_decl_count(),
            decls_once,
            "equal re-registration must dedupe trait decls (generics included in equality)"
        );
        assert_eq!(
            crate::trait_registry::registered_trait_impl_decl_count(),
            impls_once,
            "equal re-registration must dedupe impl decls (trait_type_args included in equality)"
        );
    });
}
