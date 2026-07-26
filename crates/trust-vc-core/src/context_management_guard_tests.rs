//! Guard and panic-unwind tests for context_management.rs.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::obligation_collection;
use crate::vc::VerificationContext;
use std::panic::{catch_unwind, AssertUnwindSafe};

// -- RAII guard panic-unwind safety --
//
// These tests verify that RAII guards properly restore thread-local state
// when the guarded scope panics. The Drop impl runs during stack unwind;
// if it fails (e.g., re-panics or skips restoration), state leaks across
// the catch_unwind boundary — a memory safety concern for test isolation
// and the verification pipeline's retry cascade.

#[test]
fn context_guard_restores_context_on_panic_unwind() {
    with_clean_thread_locals(|| {
        restore_context(Some(VerificationContext::new()));
        set_proof_mode(true);
        obligation_collection::record_obligation_drop();
        obligation_collection::record_obligation_drop();

        let result = catch_unwind(AssertUnwindSafe(|| {
            let _guard = save_context_guard();
            assert!(get_context().is_none(), "guard should take context");
            assert!(
                !is_in_proof_mode(),
                "guard should reset proof mode in inner scope"
            );
            assert_eq!(
                obligation_collection::obligations_dropped_count(),
                0,
                "guard should reset obligation drops in inner scope"
            );
            panic!("simulated panic inside ContextGuard scope");
        }));

        assert!(result.is_err(), "should have caught the panic");
        assert!(
            get_context().is_some(),
            "ContextGuard::drop should restore context on panic unwind"
        );
        assert!(
            is_in_proof_mode(),
            "ContextGuard::drop should restore proof mode on panic unwind"
        );
        assert_eq!(
            obligation_collection::obligations_dropped_count(),
            2,
            "ContextGuard::drop should restore obligation drops on panic unwind"
        );
    });
}

#[test]
fn broadcast_guard_resets_mode_on_panic_unwind() {
    with_clean_thread_locals(|| {
        let result = catch_unwind(AssertUnwindSafe(|| {
            let _guard = crate::broadcast_state::BroadcastGuard::enter();
            assert!(
                crate::broadcast_state::is_in_broadcast_mode(),
                "should be in broadcast mode inside guard"
            );
            panic!("simulated panic inside BroadcastGuard scope");
        }));

        assert!(result.is_err(), "should have caught the panic");
        assert!(
            !crate::broadcast_state::is_in_broadcast_mode(),
            "BroadcastGuard::drop should reset broadcast mode on panic unwind"
        );
    });
}

#[test]
fn loop_context_guard_pops_on_panic_unwind() {
    with_clean_thread_locals(|| {
        let result = catch_unwind(AssertUnwindSafe(|| {
            let _guard = crate::loop_metadata::LoopContextGuard::new(
                vec!["i".to_string()],
                "i < 10".to_string(),
            );
            assert!(
                crate::loop_metadata::current_loop_context().is_some(),
                "loop context should be active inside guard"
            );
            panic!("simulated panic inside LoopContextGuard scope");
        }));

        assert!(result.is_err(), "should have caught the panic");
        assert!(
            crate::loop_metadata::current_loop_context().is_none(),
            "LoopContextGuard::drop should pop loop context on panic unwind"
        );
    });
}

#[test]
fn invariant_mask_guard_restores_mask_on_panic_unwind() {
    with_clean_thread_locals(|| {
        restore_context(Some(VerificationContext::new()));

        // Set outer mask
        let outer_guard = enter_invariant_mask_scope(InvariantMask::Namespaces(vec![1]));
        assert_eq!(
            get_context().unwrap().invariant_mask,
            InvariantMask::Namespaces(vec![1])
        );

        let result = catch_unwind(AssertUnwindSafe(|| {
            let _inner = enter_invariant_mask_scope(InvariantMask::None);
            assert_eq!(
                get_context().unwrap().invariant_mask,
                InvariantMask::None,
                "inner scope should narrow mask"
            );
            panic!("simulated panic inside InvariantMaskGuard scope");
        }));

        assert!(result.is_err(), "should have caught the panic");
        assert_eq!(
            get_context().unwrap().invariant_mask,
            InvariantMask::Namespaces(vec![1]),
            "InvariantMaskGuard::drop should restore outer mask on panic unwind"
        );

        outer_guard.restore();
    });
}

#[test]
fn clear_all_thread_locals_resets_all_domains() {
    with_clean_thread_locals(|| {
        // Dirty up ALL thread-local domains, then verify clear_all resets them.

        // 1. Context + proof mode + obligation drops
        restore_context(Some(VerificationContext::new()));
        set_proof_mode(true);
        obligation_collection::record_obligation_drop();

        // 2. Broadcast state
        crate::broadcast_state::set_broadcast_mode(true);

        // 3. Loop context
        crate::loop_metadata::push_loop_context(vec!["x".to_string()], "x < 5".to_string());

        // 4. Mode registry
        crate::mode::register_function_mode("test_fn", crate::mode::FunctionMode::Proof);

        clear_all_thread_locals();

        // Verify all domains are clean
        assert!(get_context().is_none(), "context should be cleared");
        assert!(!is_in_proof_mode(), "proof mode should be reset");
        assert_eq!(
            obligation_collection::obligations_dropped_count(),
            0,
            "obligation drops should be reset"
        );
        assert!(
            !crate::broadcast_state::is_in_broadcast_mode(),
            "broadcast mode should be reset"
        );
        assert!(
            crate::loop_metadata::current_loop_context().is_none(),
            "loop context stack should be cleared"
        );
        assert_eq!(
            crate::mode::lookup_function_mode("test_fn"),
            crate::mode::FunctionMode::Exec,
            "mode registry should be cleared (unknown name returns Exec default)"
        );
    });
}
