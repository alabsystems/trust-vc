//! Integration tests for trigger attribute ordering (#1613).
//!
//! Tests that the attribute ordering fix preserves trigger patterns when
//! #[trigger] is processed before #[broadcast] in proc macro expansion.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verify_macro::{
    collect_obligation, get_context, register_broadcast_lemma, register_trigger, set_broadcast_mode,
};

/// DISCRIMINATING: Tests the attribute ordering fix from #1613.
///
/// When a function has `#[broadcast] #[trigger(f(n))]`, proc macro expansion
/// processes #[broadcast] (outermost) first, then #[trigger] (inner).
/// This means register_trigger() runs BEFORE set_broadcast_mode(true).
///
/// Before the fix: set_broadcast_mode(true) cleared TRIGGER_PATTERNS,
/// dropping the just-registered trigger. After the fix: triggers are
/// cleared after consumption in register_broadcast_lemma().
///
/// This test simulates the natural Verus-style attribute ordering:
/// 1. register_trigger() — from #[trigger] expansion
/// 2. set_broadcast_mode(true) — from #[broadcast] expansion
/// 3. collect_obligation() — broadcast body
/// 4. register_broadcast_lemma() — captures triggers + converts obligations
#[test]
fn test_trigger_registered_before_broadcast_mode_is_preserved() {
    common::with_clean_verification(|| {
        // Step 1: register_trigger runs FIRST (inner attribute expanded second,
        // but register_trigger is called during expansion of #[trigger])
        register_trigger(0, "f(n)".to_string());

        // Step 2: set_broadcast_mode(true) runs SECOND (outer #[broadcast])
        // Before fix: this cleared TRIGGER_PATTERNS, losing "f(n)"
        // After fix: TRIGGER_PATTERNS is NOT cleared here
        set_broadcast_mode(true);

        // Step 3: broadcast body executes, collecting ensures
        collect_obligation(
            ObligationKind::Ensures,
            "triggered_broadcast".to_string(),
            "n >= 0".to_string(),
            None,
        );

        // Step 4: register_broadcast_lemma captures triggers and converts
        register_broadcast_lemma("triggered_lemma".to_string());
        set_broadcast_mode(false);

        // Verify the trigger pattern was preserved through the ordering
        let ctx = get_context().expect("context should exist");
        let broadcast = ctx
            .obligations()
            .iter()
            .find(|o| matches!(o.kind(), ObligationKind::BroadcastAssume))
            .expect("should have a BroadcastAssume obligation");

        // The trigger_patterns must be Some with the "f(n)" pattern.
        // If set_broadcast_mode cleared triggers (the old bug), this would be None.
        assert_eq!(
            broadcast.trigger_patterns(),
            Some([vec!["f(n)".to_string()]].as_slice()),
            "Trigger registered before broadcast mode must be preserved. \
             If None, the attribute ordering bug (#1613) has regressed: \
             set_broadcast_mode(true) is clearing TRIGGER_PATTERNS."
        );
    });
}

/// Ensures triggers from one broadcast don't leak into the next.
/// After register_broadcast_lemma() consumes triggers, they must be cleared.
#[test]
fn test_trigger_cleared_after_broadcast_consumption() {
    common::with_clean_verification(|| {
        // First broadcast with trigger
        register_trigger(0, "g(x)".to_string());
        set_broadcast_mode(true);
        collect_obligation(
            ObligationKind::Ensures,
            "first_broadcast".to_string(),
            "x > 0".to_string(),
            None,
        );
        register_broadcast_lemma("first_lemma".to_string());
        set_broadcast_mode(false);

        // Second broadcast WITHOUT trigger
        set_broadcast_mode(true);
        collect_obligation(
            ObligationKind::Ensures,
            "second_broadcast".to_string(),
            "y > 0".to_string(),
            None,
        );
        register_broadcast_lemma("second_lemma".to_string());
        set_broadcast_mode(false);

        // Verify: first broadcast has trigger, second does not
        let ctx = get_context().expect("context should exist");
        let broadcasts: Vec<_> = ctx
            .obligations()
            .iter()
            .filter(|o| matches!(o.kind(), ObligationKind::BroadcastAssume))
            .collect();

        assert_eq!(broadcasts.len(), 2, "Should have 2 broadcast obligations");

        // First broadcast should have the trigger
        assert_eq!(
            broadcasts[0].trigger_patterns(),
            Some([vec!["g(x)".to_string()]].as_slice()),
            "First broadcast should have trigger pattern g(x)"
        );

        // Second broadcast must NOT have stale triggers from the first
        assert_eq!(
            broadcasts[1].trigger_patterns(),
            None,
            "Second broadcast must not inherit stale triggers from first. \
             If Some, triggers are leaking between broadcast registrations."
        );
    });
}
