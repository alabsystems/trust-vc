//! Broadcast lemma thread-local state management.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from verify_macro.rs as part of #1740 (god module splitting).
//! Owns the broadcast/trigger thread-local state (Group 3) which has zero
//! coupling to the core verification thread-locals (Group 1).

use crate::trigger_inference::TriggerInferenceMode;
use crate::vc::{BroadcastGuardClause, ObligationKind};
use std::cell::{Cell, RefCell};

// Thread-local storage for broadcast lemma mode and lemmas
thread_local! {
    /// Flag indicating whether we're currently processing a broadcast lemma.
    static IN_BROADCAST_MODE: Cell<bool> = const { Cell::new(false) };

    /// Obligation count at the moment the current broadcast body started.
    ///
    /// Used to convert only the `Ensures` obligations collected during the
    /// active broadcast body, even when other obligation kinds are interleaved.
    static BROADCAST_OBLIGATION_START: Cell<Option<usize>> = const { Cell::new(None) };

    /// Storage for registered broadcast lemmas.
    static BROADCAST_LEMMAS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };

    /// Parameter names collected during broadcast mode. Used to set `bound_vars`
    /// on BroadcastAssume obligations so the encoder quantifies only over the
    /// broadcast function's parameters, not all registered variables. Fixes #1618.
    static BROADCAST_PARAMS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };

    /// Trigger patterns collected during broadcast mode. Each entry is (group, expr).
    /// Triggers with the same group number form one multi-trigger. Different groups
    /// form alternative trigger sets. Fixes #1613.
    static TRIGGER_PATTERNS: RefCell<Vec<(u32, String)>> = const { RefCell::new(Vec::new()) };

    /// Trigger inference mode set by #[auto_trigger] (Conservative) or
    /// #[all_triggers] (Aggressive). Consumed by register_broadcast_lemma
    /// and propagated to obligations. Part of #2461 Slice 3.
    static TRIGGER_INFERENCE_MODE: Cell<Option<TriggerInferenceMode>> = const { Cell::new(None) };
}

/// RAII guard that resets broadcast mode to `false` on drop.
///
/// Guarantees `IN_BROADCAST_MODE` is reset even if the broadcast lemma body
/// panics. Matches the `ContextGuard` pattern used for proof mode. Fixes #1718.
#[must_use = "BroadcastGuard resets broadcast mode on drop — dropping immediately would enter then instantly exit"]
pub struct BroadcastGuard {
    _private: (),
}

impl BroadcastGuard {
    /// Enters broadcast mode and returns a guard that exits it on drop.
    ///
    /// Calls `set_broadcast_mode(true)` immediately. When the guard is dropped
    /// (normally or via panic unwind), calls `set_broadcast_mode(false)`.
    pub fn enter() -> Self {
        set_broadcast_mode(true);
        BroadcastGuard { _private: () }
    }
}

impl Drop for BroadcastGuard {
    fn drop(&mut self) {
        set_broadcast_mode(false);
    }
}

/// Sets whether we're currently processing a broadcast lemma.
///
/// In broadcast mode, ensures! conditions are registered as universally quantified.
/// When entering broadcast mode (true), clears the broadcast parameter list.
/// Trigger patterns are NOT cleared here — see register_broadcast_lemma().
pub fn set_broadcast_mode(mode: bool) {
    IN_BROADCAST_MODE.with(|m| m.set(mode));
    if mode {
        // Snapshot the current obligation count so registration can later
        // convert only the Ensures produced by this broadcast body. If the
        // context is not initialized yet, the first broadcast obligation starts
        // at index 0. On borrow conflict, leave the marker unset and let
        // register_broadcast_lemma fall back to the legacy trailing sweep.
        let start_idx = crate::proof_session::try_with_session(|s| {
            s.context
                .as_ref()
                .map_or(0, |context| context.obligations.len())
        })
        .ok();
        BROADCAST_OBLIGATION_START.with(|start| start.set(start_idx));

        // Graceful skip on borrow conflict: stale params may leak into the next
        // broadcast lemma, but panicking here crashes the pipeline. The next
        // clear_all_thread_locals() will clean up. Part of #1955.
        BROADCAST_PARAMS.with(|p| {
            if let Ok(mut guard) = p.try_borrow_mut() {
                guard.clear();
            }
        });
        // NOTE: Do NOT clear TRIGGER_PATTERNS here. When #[trigger] is the
        // outer attribute and #[broadcast] is inner, the proc macro expansion
        // order causes register_trigger() to execute BEFORE set_broadcast_mode(true).
        // Clearing here would silently drop all trigger patterns. Instead,
        // triggers are cleared after consumption in register_broadcast_lemma().
        // Cross-test isolation is handled by clear_all_thread_locals(). Fixes #1613.
    }
    if !mode {
        BROADCAST_OBLIGATION_START.with(|start| start.set(None));
    }
}

/// Returns whether we're currently in broadcast mode.
pub fn is_in_broadcast_mode() -> bool {
    IN_BROADCAST_MODE.with(|m| m.get())
}

/// Registers a trigger pattern for the current broadcast lemma.
///
/// Called by the expanded `#[trigger(pattern)]` macro in test mode.
/// The group number allows multiple triggers to be combined into
/// multi-trigger groups (same group = AND, different groups = OR).
/// Fixes #1613.
pub fn register_trigger(group: u32, pattern: String) {
    TRIGGER_PATTERNS.with(|t| {
        // Graceful skip on borrow conflict: trigger pattern lost → broadcast
        // may not match as precisely, but no crash. Part of #1955.
        if let Ok(mut guard) = t.try_borrow_mut() {
            guard.push((group, pattern));
        }
    });
}

/// Sets the trigger inference mode for the current broadcast scope.
///
/// Called by expanded `#[auto_trigger]` / `#[all_triggers]` macros in test mode.
/// Part of #2461 Slice 3.
pub fn set_trigger_inference_mode(mode: TriggerInferenceMode) {
    TRIGGER_INFERENCE_MODE.with(|m| m.set(Some(mode)));
}

/// Returns the current trigger inference mode without consuming it.
///
/// Used by inline quantifier construction (`ir_builder`, `ir_lowering`) to
/// capture the mode set by `#[auto_trigger]` / `#[all_triggers]` into the
/// `TrustVcExpr::Quantifier` node. Part of #2461.
pub(crate) fn get_trigger_inference_mode() -> Option<TriggerInferenceMode> {
    TRIGGER_INFERENCE_MODE.with(|m| m.get())
}

/// Tracks a broadcast parameter name.
///
/// Called from `collect_variable` in verify_macro.rs when in broadcast mode
/// to record which variables are the broadcast function's parameters.
pub(crate) fn track_broadcast_param(name: String) {
    BROADCAST_PARAMS.with(|p| {
        // Graceful skip on borrow conflict: param lost → may over-quantify,
        // but no crash. Part of #1955.
        if let Ok(mut guard) = p.try_borrow_mut() {
            guard.push(name);
        }
    });
}

/// Registers a broadcast lemma by name.
///
/// This is called after a broadcast lemma's body has been executed to collect
/// its ensures! conditions, which should be auto-applied during verification.
///
/// Sets `bound_vars` and `trigger_patterns` on the converted BroadcastAssume
/// obligations from the parameters and triggers collected during broadcast mode
/// (fixes #1618, #1613).
///
/// Requires access to `VERIFICATION_CONTEXT` via the provided closure to
/// convert Ensures obligations to BroadcastAssume.
pub fn register_broadcast_lemma(name: String) {
    register_broadcast_lemma_with_group(name, None);
}

/// Registers a broadcast lemma by name and optional group.
///
/// Grouped broadcasts are only activated when the current proof imports that
/// group via `broadcast_use!`. Ungrouped broadcasts remain globally active.
pub fn register_broadcast_lemma_with_group(name: String, group: Option<String>) {
    // Graceful skip on borrow conflict: lemma not registered → broadcast
    // not applied, but no crash. Part of #1955.
    BROADCAST_LEMMAS.with(|lemmas| {
        if let Ok(mut guard) = lemmas.try_borrow_mut() {
            guard.push(name);
        }
    });

    // Capture the broadcast function's parameter names (collected during broadcast mode).
    // Graceful fallback on borrow conflict: empty params → ground formula instead
    // of quantified one. Degraded but no crash. Part of #1955.
    let broadcast_params: Vec<String> = BROADCAST_PARAMS.with(|p| {
        p.try_borrow()
            .map(|guard| guard.clone())
            .unwrap_or_default()
    });

    // Capture trigger patterns (collected during broadcast mode via register_trigger).
    // Group triggers by group number: same group = multi-trigger (AND),
    // different groups = alternative trigger sets (OR). Fixes #1613.
    // Graceful fallback on borrow conflict: None → no triggers. Part of #1955.
    let trigger_groups: Option<Vec<Vec<String>>> = TRIGGER_PATTERNS.with(|t| {
        let Ok(triggers) = t.try_borrow() else {
            return None;
        };
        if triggers.is_empty() {
            None
        } else {
            let mut groups: std::collections::BTreeMap<u32, Vec<String>> =
                std::collections::BTreeMap::new();
            for (group, pattern) in triggers.iter() {
                groups.entry(*group).or_default().push(pattern.clone());
            }
            Some(groups.into_values().collect())
        }
    });

    let broadcast_start = BROADCAST_OBLIGATION_START.with(|start| start.get());

    // Capture trigger inference mode (#2461 Slice 3).
    let trigger_mode = TRIGGER_INFERENCE_MODE.with(|m| m.get());

    // Convert ensures! conditions from this broadcast lemma to BroadcastAssume.
    // Prefer the explicit broadcast-body start marker captured by
    // set_broadcast_mode(true). This lets us convert all Ensures from the
    // current body, even when Assume/Assert obligations are interleaved.
    // If the marker is unavailable (for example due to a borrow conflict while
    // entering broadcast mode), fall back to the legacy trailing sweep.
    // Set bound_vars to the broadcast function's parameters so the encoder
    // quantifies only over those, not all registered variables (fixes #1618).
    // Always use Some(params): empty vec -> ground formula, non-empty -> scoped quantification.
    // Using None when params is empty causes the encoder to fall back to quantifying over
    // ALL registered variables instead of producing a ground formula (fixes #1635).
    let bound = Some(broadcast_params);

    // Graceful skip on borrow conflict: ensures remains as Ensures instead of
    // BroadcastAssume → broadcast not applied, but no crash. Part of #1955.
    let _ = crate::proof_session::try_with_session_mut(|s| {
        if let Some(context) = s.context.as_mut() {
            if let Some(start_idx) = broadcast_start {
                // Harvest Requires from the broadcast body to form the guard
                // (#2575). The guard is folded into the published axiom as
                // `guard ==> body` so the postcondition is not globally true.
                let guard_clauses: Vec<BroadcastGuardClause> = context
                    .obligations
                    .iter()
                    .skip(start_idx)
                    .filter(|o| matches!(o.kind, ObligationKind::Requires))
                    .map(|o| BroadcastGuardClause {
                        condition: o.condition.clone(),
                    })
                    .collect();
                let guard = if guard_clauses.is_empty() {
                    None
                } else {
                    Some(guard_clauses)
                };

                for obligation in context.obligations.iter_mut().skip(start_idx) {
                    if matches!(obligation.kind, ObligationKind::Ensures) {
                        obligation.kind = ObligationKind::BroadcastAssume;
                        obligation.name = format!("broadcast_{}", obligation.name);
                        obligation.bound_vars = bound.clone();
                        obligation.trigger_patterns = trigger_groups.clone();
                        obligation.broadcast_group = group.clone();
                        obligation.trigger_inference_mode = trigger_mode;
                        obligation.broadcast_guard = guard.clone();
                    }
                }
            } else {
                // Legacy trailing sweep: also collect Requires adjacent to
                // Ensures so the guard is not silently dropped (#2575).
                let mut guard_clauses: Vec<BroadcastGuardClause> = Vec::new();
                let mut found_ensures = false;
                for obligation in context.obligations.iter().rev() {
                    match obligation.kind {
                        ObligationKind::Ensures => {
                            found_ensures = true;
                        }
                        ObligationKind::Requires if found_ensures => {
                            guard_clauses.push(BroadcastGuardClause {
                                condition: obligation.condition.clone(),
                            });
                        }
                        _ => break,
                    }
                }
                let guard = if guard_clauses.is_empty() {
                    None
                } else {
                    Some(guard_clauses)
                };

                for obligation in context.obligations.iter_mut().rev() {
                    if matches!(obligation.kind, ObligationKind::Ensures) {
                        obligation.kind = ObligationKind::BroadcastAssume;
                        obligation.name = format!("broadcast_{}", obligation.name);
                        obligation.bound_vars = bound.clone();
                        obligation.trigger_patterns = trigger_groups.clone();
                        obligation.broadcast_group = group.clone();
                        obligation.trigger_inference_mode = trigger_mode;
                        obligation.broadcast_guard = guard.clone();
                    } else {
                        break;
                    }
                }
            }
        }
    });
    BROADCAST_OBLIGATION_START.with(|start| start.set(None));

    // Clear trigger patterns after consumption. This prevents stale triggers
    // from leaking into subsequent broadcast lemmas within the same test.
    // Moved here from set_broadcast_mode() to fix attribute ordering bug:
    // #[broadcast] #[trigger] causes register_trigger() before set_broadcast_mode(true).
    // Graceful skip on borrow conflict: stale triggers may leak, but the next
    // clear_all_thread_locals() will clean up. Part of #1955.
    TRIGGER_PATTERNS.with(|t| {
        if let Ok(mut guard) = t.try_borrow_mut() {
            guard.clear();
        }
    });

    // Clear trigger inference mode after consumption (#2461 Slice 3).
    TRIGGER_INFERENCE_MODE.with(|m| m.set(None));
}

/// Records a `broadcast_use!` import in the active verification context.
///
/// Outside proof mode this is a no-op so runtime code does not accumulate
/// thread-local proof state.
pub fn register_broadcast_use(group: String) {
    if !crate::verify_macro::is_in_proof_mode() {
        return;
    }

    let _ = crate::proof_session::try_with_session_mut(|s| {
        let context = s
            .context
            .get_or_insert_with(crate::vc::VerificationContext::new);
        context.add_broadcast_use_group(group);
    });
}

/// Clears all broadcast-related thread-local state.
///
/// Called by `clear_all_thread_locals()` in verify_macro.rs.
pub(crate) fn clear_broadcast_state() {
    // Reset broadcast mode flag
    IN_BROADCAST_MODE.with(|m| m.set(false));
    BROADCAST_OBLIGATION_START.with(|start| start.set(None));

    // Clear broadcast lemma names.
    // Graceful skip on borrow conflict: panicking during cleanup is worse
    // than skipping — it aborts ALL subsequent clears. A skipped clear will
    // be retried by the next clear_all_thread_locals() call. Part of #1955.
    BROADCAST_LEMMAS.with(|b| {
        if let Ok(mut guard) = b.try_borrow_mut() {
            guard.clear();
            guard.shrink_to_fit();
        }
    });

    // Clear broadcast parameter tracking (fixes #1618).
    // Graceful skip on borrow conflict (Part of #1955).
    BROADCAST_PARAMS.with(|p| {
        if let Ok(mut guard) = p.try_borrow_mut() {
            guard.clear();
            guard.shrink_to_fit();
        }
    });

    // Clear trigger patterns (fixes stale trigger isolation between tests).
    // Without this, a test that crashes after register_trigger() but before
    // register_broadcast_lemma() consumes the triggers would leak stale
    // patterns into subsequent tests on the same thread.
    // Graceful skip on borrow conflict (Part of #1955).
    TRIGGER_PATTERNS.with(|t| {
        if let Ok(mut guard) = t.try_borrow_mut() {
            guard.clear();
            guard.shrink_to_fit();
        }
    });

    // Clear trigger inference mode (#2461 Slice 3).
    TRIGGER_INFERENCE_MODE.with(|m| m.set(None));
}

/// Test helpers for creating borrow-conflict scenarios.
/// These allow tests to verify that broadcast functions gracefully skip
/// operations when thread-locals are borrowed (regression tests for #1716, #1955).
#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;

    /// Holds a mutable borrow on BROADCAST_LEMMAS and calls the given closure.
    pub fn with_broadcast_lemmas_borrowed<F: FnOnce()>(f: F) {
        BROADCAST_LEMMAS.with(|b| {
            let _borrow = b.borrow_mut();
            f();
        });
    }

    /// Holds a mutable borrow on BROADCAST_PARAMS and calls the given closure.
    pub fn with_broadcast_params_borrowed<F: FnOnce()>(f: F) {
        BROADCAST_PARAMS.with(|p| {
            let _borrow = p.borrow_mut();
            f();
        });
    }

    /// Holds a mutable borrow on TRIGGER_PATTERNS and calls the given closure.
    pub fn with_trigger_patterns_borrowed<F: FnOnce()>(f: F) {
        TRIGGER_PATTERNS.with(|t| {
            let _borrow = t.borrow_mut();
            f();
        });
    }

    /// Returns the number of registered broadcast lemma names.
    pub fn broadcast_lemma_count() -> usize {
        BROADCAST_LEMMAS.with(|b| b.try_borrow().map(|v| v.len()).unwrap_or(0))
    }

    /// Returns the number of registered broadcast parameter names.
    pub fn broadcast_param_count() -> usize {
        BROADCAST_PARAMS.with(|p| p.try_borrow().map(|v| v.len()).unwrap_or(0))
    }

    /// Returns the number of registered trigger patterns.
    pub fn trigger_pattern_count() -> usize {
        TRIGGER_PATTERNS.with(|t| t.try_borrow().map(|v| v.len()).unwrap_or(0))
    }
}
