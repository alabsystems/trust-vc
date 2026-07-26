//! Broadcast registration tests for interleaved non-Ensures obligations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;
use crate::context_management::with_clean_thread_locals;
use crate::vc::ObligationKind;

#[test]
fn test_register_broadcast_lemma_converts_interleaved_ensures_in_current_body() {
    with_clean_thread_locals(|| {
        set_broadcast_mode(true);
        collect_obligation(
            ObligationKind::Ensures,
            "broadcast_post_1".to_string(),
            "n > 0".to_string(),
            None,
        );
        collect_obligation(
            ObligationKind::Assume,
            "broadcast_helper".to_string(),
            "n >= 0".to_string(),
            None,
        );
        collect_obligation(
            ObligationKind::Ensures,
            "broadcast_post_2".to_string(),
            "n < 10".to_string(),
            None,
        );

        register_broadcast_lemma("interleaved_body".to_string());
        set_broadcast_mode(false);

        let ctx = get_context().expect("context should exist");
        assert_eq!(ctx.obligations.len(), 3);
        assert_eq!(ctx.obligations[0].kind, ObligationKind::BroadcastAssume);
        assert_eq!(ctx.obligations[1].kind, ObligationKind::Assume);
        assert_eq!(ctx.obligations[2].kind, ObligationKind::BroadcastAssume);
        assert!(ctx.obligations[0].name.starts_with("broadcast_"));
        assert!(ctx.obligations[2].name.starts_with("broadcast_"));
    });
}

#[test]
fn test_register_broadcast_lemma_respects_body_start_over_preexisting_ensures() {
    with_clean_thread_locals(|| {
        collect_obligation(
            ObligationKind::Ensures,
            "earlier_post".to_string(),
            "x > 0".to_string(),
            None,
        );

        set_broadcast_mode(true);
        collect_obligation(
            ObligationKind::Ensures,
            "broadcast_post_1".to_string(),
            "n > 0".to_string(),
            None,
        );
        collect_obligation(
            ObligationKind::Assume,
            "broadcast_helper".to_string(),
            "n >= 0".to_string(),
            None,
        );
        collect_obligation(
            ObligationKind::Ensures,
            "broadcast_post_2".to_string(),
            "n < 10".to_string(),
            None,
        );

        register_broadcast_lemma("body_start_boundary".to_string());
        set_broadcast_mode(false);

        let ctx = get_context().expect("context should exist");
        assert_eq!(ctx.obligations.len(), 4);
        assert_eq!(ctx.obligations[0].kind, ObligationKind::Ensures);
        assert_eq!(ctx.obligations[1].kind, ObligationKind::BroadcastAssume);
        assert_eq!(ctx.obligations[2].kind, ObligationKind::Assume);
        assert_eq!(ctx.obligations[3].kind, ObligationKind::BroadcastAssume);
    });
}
