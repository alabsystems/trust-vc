//! Accessor and cleanup tests for context_management.rs.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::obligation_collection;
use crate::proof_session::with_session_cell;
use crate::vc::VerificationContext;

// -- ContextAccessError --

#[test]
fn context_access_error_message() {
    let err = ContextAccessError::VerificationContextBorrowed;
    assert_eq!(err.message(), "verification context is already borrowed");
}

#[test]
fn context_access_error_compatibility_panic_message() {
    let err = ContextAccessError::VerificationContextBorrowed;
    let msg = err.compatibility_panic_message("test_fn");
    assert!(
        msg.contains("CRITICAL"),
        "panic message should contain CRITICAL, got: {}",
        msg
    );
    assert!(
        msg.contains("test_fn"),
        "panic message should contain accessor name, got: {}",
        msg
    );
    assert!(
        msg.contains("already borrowed"),
        "panic message should contain borrow reason, got: {}",
        msg
    );
}

#[test]
fn context_access_error_is_copy() {
    let err = ContextAccessError::VerificationContextBorrowed;
    let err2 = err; // Copy
    assert_eq!(err, err2);
}

// -- try_clone_context --

#[test]
fn try_clone_context_returns_none_when_no_context() {
    with_clean_thread_locals(|| {
        let result = try_clone_context();
        assert!(
            matches!(result, Ok(None)),
            "should return Ok(None) when no context set"
        );
    });
}

#[test]
fn try_clone_context_returns_some_when_context_exists() {
    with_clean_thread_locals(|| {
        restore_context(Some(VerificationContext::new()));
        let result = try_clone_context();
        assert!(
            matches!(result, Ok(Some(_))),
            "should return Ok(Some(...)) when context exists"
        );
    });
}

#[test]
fn try_clone_context_returns_error_when_session_borrowed() {
    with_clean_thread_locals(|| {
        with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            let result = try_clone_context();
            assert!(
                matches!(result, Err(ContextAccessError::VerificationContextBorrowed)),
                "should return borrow error when session is mutably borrowed"
            );
        });
    });
}

// -- try_take_context --

#[test]
fn try_take_context_takes_and_empties() {
    with_clean_thread_locals(|| {
        restore_context(Some(VerificationContext::new()));

        let result = try_take_context();
        assert!(matches!(result, Ok(Some(_))), "should take the context");

        // After take, context should be None
        let after = try_clone_context();
        assert!(
            matches!(after, Ok(None)),
            "context should be None after take"
        );
    });
}

#[test]
fn try_take_context_returns_error_when_session_borrowed() {
    with_clean_thread_locals(|| {
        with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            let result = try_take_context();
            assert!(
                matches!(result, Err(ContextAccessError::VerificationContextBorrowed)),
                "should return borrow error when session is mutably borrowed"
            );
        });
    });
}

// -- take_context: graceful skip on borrow --

#[test]
fn take_context_returns_none_on_borrow_conflict() {
    with_clean_thread_locals(|| {
        restore_context(Some(VerificationContext::new()));
        with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            // take_context uses unwrap_or(None) on the error — should not panic
            let result = take_context();
            assert!(
                result.is_none(),
                "take_context should gracefully return None on borrow conflict"
            );
        });
    });
}

// -- restore_context: graceful skip on borrow --

#[test]
fn restore_context_gracefully_skips_on_borrow_conflict() {
    with_clean_thread_locals(|| {
        with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            // Should not panic — gracefully skips restoration
            restore_context(Some(VerificationContext::new()));
        });
        // After borrow released, context should still be None (restore was skipped)
        let ctx = get_context();
        assert!(
            ctx.is_none(),
            "restore_context should have been skipped during borrow conflict"
        );
    });
}

// -- ContextGuard: save/restore lifecycle --

#[test]
fn context_guard_saves_and_restores_context() {
    with_clean_thread_locals(|| {
        restore_context(Some(VerificationContext::new()));
        set_proof_mode(true);

        let guard = save_context_guard();

        // After save, context should be taken (None) and new scope starts
        let ctx_after_save = get_context();
        assert!(
            ctx_after_save.is_none(),
            "save_context_guard should take the context"
        );

        // Restore via explicit call
        guard.restore();

        // After restore, context should be back
        let ctx_restored = get_context();
        assert!(
            ctx_restored.is_some(),
            "context should be restored after guard.restore()"
        );
        let proof_mode = is_in_proof_mode();
        assert!(proof_mode, "proof mode should be restored");
    });
}

#[test]
fn context_guard_restores_on_drop() {
    with_clean_thread_locals(|| {
        restore_context(Some(VerificationContext::new()));
        set_proof_mode(false);

        {
            let _guard = save_context_guard();
            // Guard takes context and saves proof mode
            assert!(get_context().is_none(), "context taken by guard");
        }
        // Guard dropped — should restore
        assert!(
            get_context().is_some(),
            "context should be restored on guard drop"
        );
    });
}

#[test]
fn context_guard_saves_and_restores_obligation_drops() {
    with_clean_thread_locals(|| {
        // Record some drops before saving
        obligation_collection::record_obligation_drop();
        obligation_collection::record_obligation_drop();
        let before = obligation_collection::obligations_dropped_count();
        assert_eq!(before, 2, "precondition: 2 drops before save");

        let guard = save_context_guard();

        // After save, obligation drops should be reset to 0
        let during = obligation_collection::obligations_dropped_count();
        assert_eq!(during, 0, "save_context_guard should reset drops");

        // Record a drop in the inner scope
        obligation_collection::record_obligation_drop();

        guard.restore();

        // After restore, drops should be back to the saved count (2)
        let after = obligation_collection::obligations_dropped_count();
        assert_eq!(
            after, 2,
            "obligation drops should be restored to saved count"
        );
    });
}

#[test]
fn context_guard_clears_and_restores_local_let_bindings() {
    with_clean_thread_locals(|| {
        try_with_session_mut(|session| {
            session
                .local_let_bindings
                .insert("s".to_string(), "outer_seq".to_string());
        })
        .expect("precondition local binding setup should not conflict");

        let guard = save_context_guard();

        let during = try_with_session(|session| session.local_let_bindings.clone())
            .expect("inner local binding read should not conflict");
        assert!(
            during.is_empty(),
            "save_context_guard should start nested proof scopes with no inherited local let bindings"
        );

        try_with_session_mut(|session| {
            session
                .local_let_bindings
                .insert("s".to_string(), "inner_seq".to_string());
        })
        .expect("inner local binding setup should not conflict");

        guard.restore();

        let restored = try_with_session(|session| session.local_let_bindings.clone())
            .expect("restored local binding read should not conflict");
        assert_eq!(
            restored.get("s").map(String::as_str),
            Some("outer_seq"),
            "ContextGuard should restore the outer local let binding map"
        );
    });
}

// -- clear_context: graceful skip --

#[test]
fn clear_context_removes_context() {
    with_clean_thread_locals(|| {
        restore_context(Some(VerificationContext::new()));
        assert!(get_context().is_some(), "precondition: context exists");

        clear_context();

        assert!(
            get_context().is_none(),
            "clear_context should remove the context"
        );
    });
}

#[test]
fn clear_context_gracefully_skips_on_borrow_conflict() {
    with_clean_thread_locals(|| {
        restore_context(Some(VerificationContext::new()));
        with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            // Should not panic
            clear_context();
        });
        // After borrow released, context should still exist (clear was skipped)
        assert!(
            get_context().is_some(),
            "clear_context should have been skipped during borrow conflict"
        );
    });
}

// -- get_context: panic on borrow conflict --

#[test]
#[should_panic(expected = "CRITICAL")]
fn get_context_panics_on_borrow_conflict() {
    with_clean_thread_locals(|| {
        with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            // get_context calls unwrap_or_else with panic — should panic with CRITICAL
            let _ = get_context();
        });
    });
}

// -- clear_all_thread_locals: comprehensive cleanup --

#[test]
fn clear_all_thread_locals_resets_context_and_proof_mode() {
    with_clean_thread_locals(|| {
        // Dirty up state
        restore_context(Some(VerificationContext::new()));
        set_proof_mode(true);
        obligation_collection::record_obligation_drop();

        clear_all_thread_locals();

        assert!(get_context().is_none(), "context should be cleared");
        assert!(!is_in_proof_mode(), "proof mode should be reset to false");
        assert_eq!(
            obligation_collection::obligations_dropped_count(),
            0,
            "obligation drops should be reset"
        );
    });
}

// -- enter_invariant_mask_scope: borrow fallback --

#[test]
fn enter_invariant_mask_scope_returns_guard_even_on_borrow_conflict() {
    with_clean_thread_locals(|| {
        with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            // Should not panic — falls back to (None, false) guard
            let guard = enter_invariant_mask_scope(InvariantMask::None);
            // Guard with restore_enabled=false should be safe to drop
            drop(guard);
        });
    });
}

#[test]
fn enter_invariant_mask_scope_when_no_context_previously_set() {
    with_clean_thread_locals(|| {
        // No context exists yet — enter_invariant_mask_scope creates one
        let guard = enter_invariant_mask_scope(InvariantMask::Namespaces(vec![42]));

        let ctx = get_context().expect("mask scope should create a context");
        assert_eq!(ctx.invariant_mask, InvariantMask::Namespaces(vec![42]));

        // restore_enabled should be false when no prior context existed
        // So restoring should NOT try to set the mask back
        guard.restore();
    });
}
