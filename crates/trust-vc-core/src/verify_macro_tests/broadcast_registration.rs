//! Broadcast lemma registration tests: broadcast conversion, bound_vars,
//! quantification scoping.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;
use crate::context_management::with_clean_thread_locals;
use crate::vc::ObligationKind;

#[test]
fn test_register_broadcast_lemma_converts_ensures_to_broadcast_assume() {
    with_clean_thread_locals(|| {
        // Simulate broadcast lemma body: collect an Ensures obligation
        collect_obligation(
            ObligationKind::Ensures,
            "lemma_postcondition".to_string(),
            "n > 0".to_string(),
            None,
        );

        // Call register_broadcast_lemma — should convert Ensures to BroadcastAssume
        register_broadcast_lemma("test_lemma".to_string());

        let ctx = get_context().expect("context should exist");
        assert_eq!(ctx.obligations.len(), 1);
        assert_eq!(ctx.obligations[0].kind, ObligationKind::BroadcastAssume);
        assert!(ctx.obligations[0].name.starts_with("broadcast_"));
    });
}

#[test]
fn test_register_broadcast_lemma_sweep_boundary() {
    with_clean_thread_locals(|| {
        // Add a non-Ensures obligation first (boundary)
        collect_obligation(
            ObligationKind::Assert,
            "earlier_assert".to_string(),
            "true".to_string(),
            None,
        );

        // Add Ensures from broadcast body
        collect_obligation(
            ObligationKind::Ensures,
            "broadcast_post".to_string(),
            "x > 0".to_string(),
            None,
        );

        register_broadcast_lemma("sweep_test".to_string());

        let ctx = get_context().expect("context should exist");
        assert_eq!(ctx.obligations.len(), 2);
        // First obligation should still be Assert (not converted)
        assert_eq!(ctx.obligations[0].kind, ObligationKind::Assert);
        assert_eq!(ctx.obligations[0].name, "earlier_assert");
        // Second should be converted to BroadcastAssume
        assert_eq!(ctx.obligations[1].kind, ObligationKind::BroadcastAssume);
        assert!(ctx.obligations[1].name.starts_with("broadcast_"));
    });
}

// --- Broadcast bound_vars tests (fixes #1618) ---

#[test]
fn test_broadcast_lemma_sets_bound_vars() {
    // Verify that register_broadcast_lemma sets bound_vars on BroadcastAssume
    // obligations from the parameters collected during broadcast mode.
    with_clean_thread_locals(|| {
        // Simulate broadcast expansion: set mode, register params, add ensures
        set_broadcast_mode(true);
        collect_variable("n".to_string(), "u64".to_string());

        // Simulate ensures! inside broadcast body
        collect_obligation(
            ObligationKind::Ensures,
            "sum_nonneg_ensures_0".to_string(),
            "sum(n) >= 0".to_string(),
            None,
        );

        // Register the broadcast lemma — this converts Ensures to BroadcastAssume
        register_broadcast_lemma("lemma_sum_nonneg".to_string());
        set_broadcast_mode(false);

        let ctx = get_context().expect("context should exist");
        let broadcast_obligations: Vec<_> = ctx
            .obligations
            .iter()
            .filter(|o| matches!(o.kind, ObligationKind::BroadcastAssume))
            .collect();

        assert_eq!(
            broadcast_obligations.len(),
            1,
            "Expected 1 BroadcastAssume obligation"
        );

        let bound = broadcast_obligations[0].bound_vars.as_ref();
        assert!(
            bound.is_some(),
            "BroadcastAssume should have bound_vars set"
        );
        assert_eq!(
            bound.unwrap(),
            &vec!["n".to_string()],
            "bound_vars should be ['n'], the broadcast function's parameter"
        );
    });
}

#[test]
fn test_broadcast_bound_vars_excludes_non_broadcast_variables() {
    // When a function has variables x, y AND a broadcast lemma has parameter n,
    // the broadcast's bound_vars should only contain n, not x or y.
    with_clean_thread_locals(|| {
        // First: register the calling function's variables (outside broadcast mode)
        collect_variable("x".to_string(), "i32".to_string());
        collect_variable("y".to_string(), "i32".to_string());

        // Now simulate a broadcast lemma with parameter n
        set_broadcast_mode(true);
        collect_variable("n".to_string(), "u64".to_string());

        collect_obligation(
            ObligationKind::Ensures,
            "broadcast_ensures".to_string(),
            "n >= 0".to_string(),
            None,
        );

        register_broadcast_lemma("lemma_n_nonneg".to_string());
        set_broadcast_mode(false);

        let ctx = get_context().expect("context should exist");
        let broadcast = ctx
            .obligations
            .iter()
            .find(|o| matches!(o.kind, ObligationKind::BroadcastAssume))
            .expect("should have BroadcastAssume");

        let bound = broadcast
            .bound_vars
            .as_ref()
            .expect("should have bound_vars");
        assert_eq!(
            bound,
            &vec!["n".to_string()],
            "bound_vars should only contain 'n', not 'x' or 'y'"
        );
        assert!(
            !bound.contains(&"x".to_string()),
            "x should NOT be in bound_vars"
        );
        assert!(
            !bound.contains(&"y".to_string()),
            "y should NOT be in bound_vars"
        );

        // Verify all 3 variables are in the context (x, y, n)
        assert_eq!(
            ctx.variables.len(),
            3,
            "Context should have all 3 variables (x, y, n)"
        );
    });
}

#[test]
fn test_register_broadcast_lemma_zero_params_produces_some_empty() {
    // Regression test for #1635: register_broadcast_lemma must produce
    // bound_vars: Some(vec![]) for zero-parameter broadcasts, causing
    // the encoder to assert the condition as a ground formula.
    // Previously, empty params mapped to None, which caused the encoder
    // to fall back to quantifying over ALL registered variables.
    use crate::verify_macro::{collect_obligation, register_broadcast_lemma, set_broadcast_mode};

    with_clean_thread_locals(|| {
        // Enter broadcast mode with ZERO parameters — no collect_variable calls
        set_broadcast_mode(true);

        // Add an ensures condition (this gets converted to BroadcastAssume)
        collect_obligation(
            ObligationKind::Ensures,
            "ground_truth".to_string(),
            "true".to_string(),
            None,
        );

        // register_broadcast_lemma captures BROADCAST_PARAMS (empty) and
        // converts Ensures -> BroadcastAssume with bound_vars
        register_broadcast_lemma("zero_param_broadcast".to_string());
        set_broadcast_mode(false);

        // Inspect the obligation to check bound_vars (#2481: use proof_session)
        crate::proof_session::with_session_cell(|cell| {
            let session = cell.borrow();
            let context = session.context.as_ref().expect("context should exist");
            let broadcast = context
                .obligations
                .iter()
                .find(|o| matches!(o.kind, ObligationKind::BroadcastAssume))
                .expect("should have a BroadcastAssume obligation");

            // #1635 fix: empty params -> Some(vec![]) -> ground formula (not over-quantified)
            assert_eq!(
                broadcast.bound_vars,
                Some(vec![]),
                "Zero-parameter broadcast should have bound_vars: Some(vec![]) \
                 so the encoder asserts as ground formula, not over-quantified."
            );
        });
    });
}

/// BroadcastGuard resets broadcast mode on normal drop (RAII). Fixes #1718.
#[test]
fn test_broadcast_guard_resets_mode_on_drop() {
    with_clean_thread_locals(|| {
        assert!(!is_in_broadcast_mode());

        {
            let _guard = BroadcastGuard::enter();
            assert!(is_in_broadcast_mode());
        }
        // Guard dropped — mode must be false.
        assert!(!is_in_broadcast_mode());
    });
}

/// BroadcastGuard resets broadcast mode even when the body panics. Fixes #1718.
#[test]
fn test_broadcast_guard_resets_mode_on_panic() {
    with_clean_thread_locals(|| {
        let result = std::panic::catch_unwind(|| {
            let _guard = BroadcastGuard::enter();
            assert!(is_in_broadcast_mode());
            panic!("simulated broadcast body panic");
        });

        assert!(result.is_err(), "should have panicked");
        // Guard's Drop ran during unwind — mode must be false.
        assert!(
            !is_in_broadcast_mode(),
            "BroadcastGuard must reset broadcast mode on panic unwind (#1718)"
        );
    });
}

// --- End-to-end pipeline tests: macro pipeline → ay (#1638) ---

/// DISCRIMINATING (#1635): Zero-param broadcast through pipeline → ground
/// formula. Paired with negative test to prove non-triviality.
#[test]
fn test_broadcast_zero_params_end_to_end_verifies() {
    with_clean_thread_locals(|| {
        collect_variable("x".to_string(), "i32".to_string());
        set_broadcast_mode(true);
        collect_obligation(
            ObligationKind::Ensures,
            "ground_ensures".into(),
            "x > 0".into(),
            None,
        );
        register_broadcast_lemma("zero_param_lemma".to_string());
        set_broadcast_mode(false);
        collect_obligation(
            ObligationKind::Assert,
            "check_positive".into(),
            "x > 0".into(),
            None,
        );
        let result = verify_collected();
        assert!(
            matches!(result, crate::encoder::VerifyResult::Verified),
            "Zero-param broadcast pipeline should verify x>0, got: {:?}",
            result
        );
    });
}

/// DISCRIMINATING: Negative — broadcast x > 0 must NOT prove x < 0.
#[test]
fn test_broadcast_zero_params_end_to_end_negative() {
    with_clean_thread_locals(|| {
        collect_variable("x".to_string(), "i32".to_string());
        set_broadcast_mode(true);
        collect_obligation(
            ObligationKind::Ensures,
            "ground_ensures".into(),
            "x > 0".into(),
            None,
        );
        register_broadcast_lemma("zero_param_lemma".to_string());
        set_broadcast_mode(false);
        collect_obligation(
            ObligationKind::Assert,
            "check_negative".into(),
            "x < 0".into(),
            None,
        );
        let result = verify_collected();
        assert!(
            !matches!(result, crate::encoder::VerifyResult::Verified),
            "Broadcast x>0 must not prove x<0, got: {:?}",
            result
        );
    });
}

/// DISCRIMINATING: One-param broadcast with extra variable in scope.
/// Broadcast axiom `n == n` applied as `forall n: n == n`; assertion
/// checks `y == y` for non-broadcast variable y. Uses tautological body
/// to avoid vacuous truth from contradictory "forall n: n > 0" (#2258).
/// Tests broadcast registration and instantiation mechanics.
#[test]
fn test_broadcast_one_param_end_to_end_verifies() {
    with_clean_thread_locals(|| {
        collect_variable("y".to_string(), "i32".to_string());
        set_broadcast_mode(true);
        collect_variable("n".to_string(), "i32".to_string());
        collect_obligation(
            ObligationKind::Ensures,
            "broadcast_ensures".into(),
            "n == n".into(),
            None,
        );
        register_broadcast_lemma("one_param_lemma".to_string());
        set_broadcast_mode(false);
        collect_obligation(
            ObligationKind::Assert,
            "check_via_broadcast".into(),
            "y == y".into(),
            None,
        );
        let result = verify_collected();
        assert!(
            matches!(result, crate::encoder::VerifyResult::Verified),
            "One-param broadcast should verify y==y via forall n: n==n, got: {:?}",
            result
        );
    });
}
