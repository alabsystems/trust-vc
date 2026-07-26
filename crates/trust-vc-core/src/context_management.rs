//! Verification context lifecycle management.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from verify_macro.rs as part of #1740 (god module splitting).
//! Contains take/restore/save/clear/get operations on the thread-local
//! verification context — RAII guard, cleanup, and context inspection.

use crate::proof_session::{try_with_session, try_with_session_mut};
use crate::vc::{InvariantMask, VerificationContext};
use crate::verify_macro::{is_in_proof_mode, set_proof_mode};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ContextAccessError {
    VerificationContextBorrowed,
}

impl ContextAccessError {
    pub(crate) fn message(self) -> &'static str {
        match self {
            Self::VerificationContextBorrowed => "verification context is already borrowed",
        }
    }

    fn compatibility_panic_message(self, accessor: &str) -> String {
        format!(
            "CRITICAL: {accessor} cannot continue because {}",
            self.message()
        )
    }
}

/// Clones the current verification context while distinguishing an empty slot
/// from a RefCell borrow conflict at the public verification boundary.
pub(crate) fn try_clone_context() -> Result<Option<VerificationContext>, ContextAccessError> {
    try_with_session(|s| s.context.clone())
        .map_err(|_| ContextAccessError::VerificationContextBorrowed)
}

/// Takes the current verification context while distinguishing an empty slot
/// from a RefCell borrow conflict at the public verification boundary.
pub(crate) fn try_take_context() -> Result<Option<VerificationContext>, ContextAccessError> {
    try_with_session_mut(|s| s.context.take())
        .map_err(|_| ContextAccessError::VerificationContextBorrowed)
}

/// Takes the thread-local verification context, leaving None in its place.
///
/// Used by `#[proof]` expansion to save/restore context across nested calls.
/// Each proof function gets a fresh scope; the outer scope is restored after.
pub fn take_context() -> Option<VerificationContext> {
    // Compatibility shim: proof-scope save/restore keeps the graceful-skip
    // behavior from #1955. Public verification boundaries must use the
    // explicit `try_take_context()` helper instead.
    try_take_context().unwrap_or(None)
}

/// Restores a previously saved verification context.
///
/// Used by `#[proof]` expansion to restore the outer scope after nested calls.
pub fn restore_context(saved: Option<VerificationContext>) {
    // Graceful skip on borrow conflict: outer context not restored →
    // stale inner context remains until next clear_all_thread_locals().
    // Part of #1955.
    let _ = try_with_session_mut(|s| {
        s.context = saved;
    });
}

/// RAII guard that restores verification context and proof mode on drop.
///
/// Guarantees context restoration even when the proof function body panics.
/// Created by [`save_context_guard`]; restored automatically via `Drop`.
#[must_use = "ContextGuard restores context on drop — dropping immediately would save then instantly restore"]
pub struct ContextGuard {
    saved_ctx: Option<Option<VerificationContext>>,
    saved_proof_mode: Option<bool>,
    saved_obligation_drops: Option<usize>,
    saved_local_let_bindings: Option<HashMap<String, String>>,
}

impl ContextGuard {
    fn do_restore(&mut self) {
        if let Some(ctx) = self.saved_ctx.take() {
            restore_context(ctx);
        }
        if let Some(bindings) = self.saved_local_let_bindings.take() {
            let _ = try_with_session_mut(|s| {
                s.local_let_bindings = bindings;
            });
        }
        if let Some(mode) = self.saved_proof_mode.take() {
            set_proof_mode(mode);
        }
        if let Some(count) = self.saved_obligation_drops.take() {
            crate::obligation_collection::set_obligations_dropped_count(count);
        }
    }

    /// Explicitly consumes the guard, restoring context and proof mode.
    /// Prefer this over letting the guard drop implicitly for clarity.
    pub fn restore(mut self) {
        self.do_restore();
    }
}

impl Drop for ContextGuard {
    fn drop(&mut self) {
        self.do_restore();
    }
}

/// RAII guard that restores the previous invariant mask on drop.
///
/// Used by `#[opens_invariants(...)]` expansion so nested function calls can
/// temporarily narrow the allowed invariant set without permanently clobbering
/// the caller's mask.
#[must_use = "InvariantMaskGuard restores the previous mask on drop"]
pub struct InvariantMaskGuard {
    saved_mask: Option<InvariantMask>,
    restore_enabled: bool,
}

impl InvariantMaskGuard {
    fn do_restore(&mut self) {
        if self.restore_enabled {
            if let Some(mask) = self.saved_mask.take() {
                let _ = try_with_session_mut(|s| {
                    let context = s.context.get_or_insert_with(VerificationContext::new);
                    context.set_invariant_mask(mask);
                });
            }
        } else {
            self.saved_mask = None;
        }
    }

    /// Explicitly consumes the guard and restores the previous mask.
    pub fn restore(mut self) {
        self.do_restore();
    }
}

impl Drop for InvariantMaskGuard {
    fn drop(&mut self) {
        self.do_restore();
    }
}

/// Sets the current invariant mask and returns a guard that restores the
/// previous mask on drop.
pub fn enter_invariant_mask_scope(mask: InvariantMask) -> InvariantMaskGuard {
    let (saved_mask, restore_enabled) = try_with_session_mut(|s| {
        let had_context = s.context.is_some();
        let context = s.context.get_or_insert_with(VerificationContext::new);
        (
            Some(std::mem::replace(&mut context.invariant_mask, mask)),
            had_context,
        )
    })
    .unwrap_or((None, false));

    InvariantMaskGuard {
        saved_mask,
        restore_enabled,
    }
}

/// Saves the current verification context and proof mode, returning a guard
/// that restores both on drop. This is panic-safe: if the proof function
/// body panics, the `Drop` impl ensures the outer context is restored.
pub fn save_context_guard() -> ContextGuard {
    let saved_ctx = Some(take_context());
    let saved_proof_mode = Some(is_in_proof_mode());
    let saved_obligation_drops = Some(crate::obligation_collection::obligations_dropped_count());
    let saved_local_let_bindings = try_with_session_mut(|s| {
        let saved = s.local_let_bindings.clone();
        s.local_let_bindings.clear();
        saved
    })
    .ok();
    crate::obligation_collection::reset_obligations_dropped();
    ContextGuard {
        saved_ctx,
        saved_proof_mode,
        saved_obligation_drops,
        saved_local_let_bindings,
    }
}

/// Clears the thread-local verification context.
///
/// Useful for resetting between test cases.
pub fn clear_context() {
    // Graceful skip on borrow conflict: panicking during cleanup aborts
    // ALL subsequent clears in clear_all_thread_locals. A skipped clear
    // will be retried by the next cleanup call. Part of #1955.
    let _ = try_with_session_mut(|s| {
        s.context = None;
    });
}

/// Clears all thread-local storage used by the verification system.
///
/// This function should be called at the end of each test to prevent
/// memory leaks from accumulated verification state.
pub fn clear_all_thread_locals() {
    // Clear the proof session (context, proof mode, local var types, scope
    // stack, translator state, pre-built expr cache, obligation counters).
    // Graceful skip on borrow conflict (Part of #1955, #2481).
    let _ = crate::proof_session::clear_proof_session();

    // Clear all broadcast-related thread-locals (fixes #1520, #1618, #1613)
    crate::broadcast_state::clear_broadcast_state();

    // Clear extern spec contracts and registered proofs (fixes #1560 finding).
    // These thread-locals live in other modules but must be cleared here to
    // prevent state leakage when callers use only clear_all_thread_locals().
    crate::extern_spec_verify::clear_extern_contracts();
    crate::verification_bridge::clear_registrations();

    // Clear the MODE_REGISTRY thread-local in mode.rs.
    // Function-mode registrations (Exec/Spec/Proof) accumulate across tests
    // when only clear_all_thread_locals() is used for cleanup. Gap found by
    // P1#219 memory_verification audit.
    crate::mode::clear_mode_registry();

    // PREPARED_CONDITIONS thread-local was removed as part of #2219.
    // The typed verification path passes TrustVcExpr directly on
    // PreparedObligation — no thread-local lookup needed.

    // Clear loop context stack. Auto-inferred loop metadata uses a
    // push/pop stack that must not leak between tests. Part of #2502.
    crate::loop_metadata::clear_loop_context_stack();

    // Clear registered trait metadata. Without this, TraitCatalog entries
    // accumulate across tests running on the same thread.
    crate::trait_registry::clear_registered_traits();
}

/// Gets a copy of the current verification context for inspection.
///
/// Returns None if no context has been initialized.
///
/// Panics with a `CRITICAL:` diagnostic if the context is currently borrowed so
/// callers cannot confuse "empty" with "locked".
#[allow(clippy::panic)] // intentional: CRITICAL diagnostic on borrow conflict
pub fn get_context() -> Option<VerificationContext> {
    try_clone_context().unwrap_or_else(|err| {
        // Deliberate compatibility boundary: borrowed context is distinct from no context.
        panic!("{}", err.compatibility_panic_message("get_context")) // quality-audit: allow-panic
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_invariant_mask_guard_sets_and_restores_previous_mask() {
        clear_all_thread_locals();

        let outer = enter_invariant_mask_scope(InvariantMask::Namespaces(vec![1]));
        assert_eq!(
            get_context()
                .expect("mask scope should initialize a context")
                .invariant_mask,
            InvariantMask::Namespaces(vec![1])
        );

        {
            let inner = enter_invariant_mask_scope(InvariantMask::None);
            assert_eq!(
                get_context()
                    .expect("nested mask scope should keep the context")
                    .invariant_mask,
                InvariantMask::None
            );
            inner.restore();
        }

        assert_eq!(
            get_context()
                .expect("outer scope should restore after inner scope")
                .invariant_mask,
            InvariantMask::Namespaces(vec![1])
        );

        outer.restore();
        assert_eq!(
            get_context()
                .expect("restoring the outer scope should keep the context")
                .invariant_mask,
            InvariantMask::Namespaces(vec![1])
        );
    }
}

/// Panic-safe wrapper for tests that use thread-local verification state.
///
/// Clears all thread-locals before and after `f`, catching panics so that
/// cleanup always runs. Re-raises the panic after cleanup. Use this in
/// `#[test]` functions instead of bare `clear_all_thread_locals()` bookends
/// to prevent state leakage when a test panics. Part of #2714.
#[cfg(test)]
pub(crate) fn with_clean_thread_locals<F: FnOnce()>(f: F) {
    clear_all_thread_locals();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    clear_all_thread_locals();
    match result {
        Ok(()) => {}
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

#[cfg(test)]
#[path = "context_management_proof_tests.rs"]
mod proof_tests;
