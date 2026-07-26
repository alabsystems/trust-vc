//! Proof coverage tests for proof_session.rs
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Covers previously untested production paths: borrow-conflict fallbacks,
//! PENDING_OBLIGATION_DROPS Cell accounting, sync_pending_obligation_drops
//! merging, and session lifecycle management.
//!
//! Wiring: Worker must add to proof_session.rs:
//!   #[cfg(test)]
//!   #[path = "proof_session_proof_tests.rs"]
//!   mod proof_tests;
//!
//! Part of #949.

use super::*;

// -- ProofSession::new: field initialization --

#[test]
fn new_session_has_no_context() {
    clear_proof_session().ok();
    let result = try_with_session(|session| session.context.is_none());
    assert_eq!(result, Ok(true), "new session should have context = None");
    clear_proof_session().ok();
}

#[test]
fn new_session_not_in_proof_mode() {
    clear_proof_session().ok();
    let result = try_with_session(|session| session.in_proof_mode);
    assert_eq!(
        result,
        Ok(false),
        "new session should have in_proof_mode = false"
    );
    clear_proof_session().ok();
}

#[test]
fn new_session_has_empty_local_var_types() {
    clear_proof_session().ok();
    let result = try_with_session(|session| session.local_var_types.is_empty());
    assert_eq!(
        result,
        Ok(true),
        "new session should have empty local_var_types"
    );
    clear_proof_session().ok();
}

#[test]
fn new_session_has_zero_obligations_collected() {
    clear_proof_session().ok();
    let result = try_with_session(|session| session.total_obligations_collected.get());
    assert_eq!(
        result,
        Ok(0),
        "new session should have 0 total_obligations_collected"
    );
    clear_proof_session().ok();
}

#[test]
fn new_session_has_zero_obligations_dropped() {
    clear_proof_session().ok();
    let count = obligations_dropped_count();
    assert_eq!(count, 0, "new session should have 0 obligations_dropped");
    clear_proof_session().ok();
}

// -- SessionBorrowError: Display via thiserror --

#[test]
fn session_borrow_error_display_messages() {
    let shared_err = SessionBorrowError::SharedAccessUnavailable;
    assert_eq!(
        shared_err.to_string(),
        "proof session is already mutably borrowed"
    );

    let mut_err = SessionBorrowError::MutableAccessUnavailable;
    assert_eq!(mut_err.to_string(), "proof session is already borrowed");
}

#[test]
fn session_borrow_error_is_copy() {
    let err = SessionBorrowError::SharedAccessUnavailable;
    let err2 = err; // Copy
    assert_eq!(err, err2, "SessionBorrowError should be Copy");
}

// -- try_with_session: shared borrow --

#[test]
fn try_with_session_returns_closure_result() {
    clear_proof_session().ok();
    let result = try_with_session(|_session| 42);
    assert_eq!(
        result,
        Ok(42),
        "try_with_session should return closure value"
    );
    clear_proof_session().ok();
}

#[test]
fn try_with_session_fails_when_mutably_borrowed() {
    clear_proof_session().ok();
    with_session_cell(|cell| {
        let _mut_borrow = cell.borrow_mut();
        let result = try_with_session(|_| ());
        assert_eq!(
            result,
            Err(SessionBorrowError::SharedAccessUnavailable),
            "shared access should fail when session is mutably borrowed"
        );
    });
    clear_proof_session().ok();
}

// -- try_with_session_mut: mutable borrow --

#[test]
fn try_with_session_mut_returns_closure_result() {
    clear_proof_session().ok();
    let result = try_with_session_mut(|_session| "hello");
    assert_eq!(
        result,
        Ok("hello"),
        "try_with_session_mut should return closure value"
    );
    clear_proof_session().ok();
}

#[test]
fn try_with_session_mut_fails_when_already_borrowed() {
    clear_proof_session().ok();
    with_session_cell(|cell| {
        let _shared_borrow = cell.borrow();
        let result = try_with_session_mut(|_| ());
        assert_eq!(
            result,
            Err(SessionBorrowError::MutableAccessUnavailable),
            "mutable access should fail when session has a shared borrow"
        );
    });
    clear_proof_session().ok();
}

#[test]
fn try_with_session_mut_fails_when_mutably_borrowed() {
    clear_proof_session().ok();
    with_session_cell(|cell| {
        let _mut_borrow = cell.borrow_mut();
        let result = try_with_session_mut(|_| ());
        assert_eq!(
            result,
            Err(SessionBorrowError::MutableAccessUnavailable),
            "mutable access should fail when session is already mutably borrowed"
        );
    });
    clear_proof_session().ok();
}

// -- clear_proof_session --

#[test]
fn clear_proof_session_resets_session_state() {
    clear_proof_session().ok();
    // Dirty the session
    try_with_session_mut(|session| {
        session.in_proof_mode = true;
        session
            .local_var_types
            .insert("x".to_string(), TrustVcType::Bool);
    })
    .unwrap();

    // Verify dirty state
    let is_dirty = try_with_session(|session| session.in_proof_mode).unwrap();
    assert!(is_dirty, "session should be in proof mode before clear");

    // Clear
    clear_proof_session().unwrap();

    // Verify reset
    let is_clean =
        try_with_session(|session| !session.in_proof_mode && session.local_var_types.is_empty())
            .unwrap();
    assert!(is_clean, "session should be fully reset after clear");
    clear_proof_session().ok();
}

#[test]
fn clear_proof_session_also_clears_pending_drops() {
    clear_proof_session().ok();
    // Force some pending drops by recording while borrowed
    with_session_cell(|cell| {
        let _mut_borrow = cell.borrow_mut();
        record_obligation_drop();
        record_obligation_drop();
    });

    // Pending should be 2 (only in Cell since session was borrowed)
    // Now clear everything
    clear_proof_session().unwrap();

    // After clear, count should be 0 (pending was cleared too)
    let count = obligations_dropped_count();
    assert_eq!(
        count, 0,
        "clear_proof_session must also reset PENDING_OBLIGATION_DROPS"
    );
    clear_proof_session().ok();
}

// -- record_obligation_drop: happy path --

#[test]
fn record_obligation_drop_increments_session_count() {
    clear_proof_session().ok();
    record_obligation_drop();
    record_obligation_drop();
    record_obligation_drop();

    let count = obligations_dropped_count();
    assert_eq!(count, 3, "three calls should yield count of 3");
    clear_proof_session().ok();
}

// -- record_obligation_drop: borrow-conflict fallback to Cell --

#[test]
fn record_obligation_drop_falls_back_to_cell_when_session_borrowed() {
    clear_proof_session().ok();
    with_session_cell(|cell| {
        let _mut_borrow = cell.borrow_mut();
        // Session is mutably borrowed — record_obligation_drop cannot get
        // a shared borrow, so it must fall back to PENDING_OBLIGATION_DROPS
        record_obligation_drop();
        record_obligation_drop();
    });
    // After the mutable borrow is released, obligations_dropped_count
    // should sync the pending drops into the session
    let count = obligations_dropped_count();
    assert_eq!(
        count, 2,
        "drops recorded via Cell fallback should be synced into session count"
    );
    clear_proof_session().ok();
}

// -- sync_pending_obligation_drops: merging --

#[test]
fn sync_merges_pending_drops_into_session_on_next_access() {
    clear_proof_session().ok();

    // Record 1 drop normally
    record_obligation_drop();

    // Record 2 drops via fallback (while session is borrowed)
    with_session_cell(|cell| {
        let _mut_borrow = cell.borrow_mut();
        record_obligation_drop();
        record_obligation_drop();
    });

    // Now read the count — sync_pending_obligation_drops should merge
    let count = obligations_dropped_count();
    assert_eq!(
        count, 3,
        "1 direct + 2 pending should merge to 3 on next read"
    );

    // Verify pending is drained (second read should return same count)
    let count2 = obligations_dropped_count();
    assert_eq!(
        count2, 3,
        "second read should still be 3 (pending was drained, not double-counted)"
    );
    clear_proof_session().ok();
}

// -- obligations_dropped_count: fallback when session borrowed --

#[test]
fn obligations_dropped_count_returns_pending_when_session_borrowed() {
    clear_proof_session().ok();
    with_session_cell(|cell| {
        let _mut_borrow = cell.borrow_mut();
        // Record directly to pending
        record_obligation_drop();
        record_obligation_drop();
        record_obligation_drop();

        // Read count while session is still borrowed — should read from Cell
        let count = obligations_dropped_count();
        assert_eq!(
            count, 3,
            "obligations_dropped_count should read from PENDING_OBLIGATION_DROPS \
             when session is borrowed"
        );
    });
    clear_proof_session().ok();
}

// -- set_obligations_dropped_count: happy path --

#[test]
fn set_obligations_dropped_count_updates_session() {
    clear_proof_session().ok();
    set_obligations_dropped_count(42);
    let count = obligations_dropped_count();
    assert_eq!(
        count, 42,
        "set_obligations_dropped_count should update session count"
    );
    clear_proof_session().ok();
}

#[test]
fn set_obligations_dropped_count_clears_pending_on_success() {
    clear_proof_session().ok();
    // First, create some pending drops
    with_session_cell(|cell| {
        let _mut_borrow = cell.borrow_mut();
        record_obligation_drop();
        record_obligation_drop();
    });

    // Now set count (session is available) — should overwrite AND clear pending
    set_obligations_dropped_count(10);

    let count = obligations_dropped_count();
    assert_eq!(
        count, 10,
        "set should overwrite (not add) and clear pending drops"
    );
    clear_proof_session().ok();
}

// -- set_obligations_dropped_count: borrow-conflict fallback --

#[test]
fn set_obligations_dropped_count_falls_back_to_cell_when_session_borrowed() {
    clear_proof_session().ok();
    with_session_cell(|cell| {
        let _mut_borrow = cell.borrow_mut();
        set_obligations_dropped_count(99);

        // Read via fallback too — should see 99 in pending
        let count = obligations_dropped_count();
        assert_eq!(
            count, 99,
            "set via Cell fallback should be readable via Cell fallback"
        );
    });
    // After borrow released, sync should merge 99 into session
    let count = obligations_dropped_count();
    assert_eq!(
        count, 99,
        "pending count should be synced into session after borrow release"
    );
    clear_proof_session().ok();
}

// -- reset_obligations_dropped --

#[test]
fn reset_obligations_dropped_sets_count_to_zero() {
    clear_proof_session().ok();
    record_obligation_drop();
    record_obligation_drop();

    let before = obligations_dropped_count();
    assert_eq!(before, 2, "precondition: should have 2 drops");

    reset_obligations_dropped();

    let after = obligations_dropped_count();
    assert_eq!(after, 0, "reset should bring count to 0");
    clear_proof_session().ok();
}

// -- Full borrow-conflict cascade --

#[test]
fn full_cascade_record_while_borrowed_then_read_after_release() {
    clear_proof_session().ok();

    // Phase 1: record 2 drops normally
    record_obligation_drop();
    record_obligation_drop();

    // Phase 2: record 3 drops while session is borrowed (Cell fallback)
    with_session_cell(|cell| {
        let _mut_borrow = cell.borrow_mut();
        record_obligation_drop();
        record_obligation_drop();
        record_obligation_drop();
    });

    // Phase 3: read count — sync should merge 2 (session) + 3 (pending) = 5
    let count = obligations_dropped_count();
    assert_eq!(
        count, 5,
        "full cascade: 2 direct + 3 pending should yield 5"
    );

    // Phase 4: set to explicit value, then record more via fallback
    set_obligations_dropped_count(100);
    with_session_cell(|cell| {
        let _mut_borrow = cell.borrow_mut();
        record_obligation_drop();
    });
    let final_count = obligations_dropped_count();
    assert_eq!(final_count, 101, "100 set + 1 pending = 101 after sync");

    clear_proof_session().ok();
}

// -- Default impl --

#[test]
fn proof_session_default_matches_new() {
    let from_new = ProofSession::new();
    let from_default = ProofSession::default();
    // Compare structural fields (ProofSession doesn't derive PartialEq)
    assert_eq!(from_new.in_proof_mode, from_default.in_proof_mode);
    assert!(from_new.context.is_none() && from_default.context.is_none());
    assert!(from_new.local_var_types.is_empty() && from_default.local_var_types.is_empty());
    assert_eq!(
        from_new.total_obligations_collected.get(),
        from_default.total_obligations_collected.get()
    );
    assert_eq!(
        from_new.obligations_dropped.get(),
        from_default.obligations_dropped.get()
    );
}
