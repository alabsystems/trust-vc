//! Protocol-registration verification bridge tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

/// clear_registrations must not panic when protocol thread-locals are borrowed.
///
/// Before this fix, the protocol thread-locals (STATE_VARS, ACTIONS,
/// INVARIANTS, LIVENESS) used bare `borrow_mut()` in clear_registrations(),
/// which would double-panic-abort if called during unwind while any of
/// these RefCells were already borrowed. The graceful `try_borrow_mut()`
/// pattern from #1955 was applied to REGISTERED_PROOFS but missed for
/// the protocol thread-locals.
#[test]
fn test_clear_registrations_graceful_under_protocol_borrow_conflict() {
    with_cleared_registrations(|| {
        register_protocol_components();

        // Simulate a borrow conflict: PROTOCOL_STATE_VARS is held while
        // clear_registrations runs. Without the try_borrow_mut fix, this panics.
        with_protocol_state_vars_borrowed(|| {
            clear_registrations();
        });

        // STATE_VARS was skipped (still borrowed), but the other protocol
        // thread-locals must still clear so cleanup continues.
        assert_protocol_component_counts(1, 0, 0, 0);
        clear_registrations();
        assert_protocol_component_counts(0, 0, 0, 0);
    });
}

#[test]
fn test_clear_registrations_graceful_under_protocol_actions_borrow_conflict() {
    with_cleared_registrations(|| {
        register_protocol_components();

        with_protocol_actions_borrowed(|| {
            clear_registrations();
        });

        assert_protocol_component_counts(0, 1, 0, 0);
        clear_registrations();
        assert_protocol_component_counts(0, 0, 0, 0);
    });
}

#[test]
fn test_clear_registrations_graceful_under_protocol_invariants_borrow_conflict() {
    with_cleared_registrations(|| {
        register_protocol_components();

        with_protocol_invariants_borrowed(|| {
            clear_registrations();
        });

        assert_protocol_component_counts(0, 0, 1, 0);
        clear_registrations();
        assert_protocol_component_counts(0, 0, 0, 0);
    });
}

#[test]
fn test_clear_registrations_graceful_under_protocol_liveness_borrow_conflict() {
    with_cleared_registrations(|| {
        register_protocol_components();

        with_protocol_liveness_borrowed(|| {
            clear_registrations();
        });

        assert_protocol_component_counts(0, 0, 0, 1);
        clear_registrations();
        assert_protocol_component_counts(0, 0, 0, 0);
    });
}

#[cfg(feature = "ty")]
#[test]
fn test_clear_registrations_graceful_under_protocol_obligations_borrow_conflict() {
    with_cleared_registrations(|| {
        register_protocol(test_protocol_obligation("TestProto"));
        register_protocol_components();

        with_protocol_obligations_borrowed(|| {
            clear_registrations();
        });

        PROTOCOL_OBLIGATIONS.with(|v| {
            assert_eq!(v.borrow().len(), 1);
        });
        assert_protocol_component_counts(0, 0, 0, 0);
        clear_registrations();
        PROTOCOL_OBLIGATIONS.with(|v| {
            assert_eq!(v.borrow().len(), 0);
        });
    });
}
