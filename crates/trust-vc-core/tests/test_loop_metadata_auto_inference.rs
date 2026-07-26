//! Tests for auto-inferred loop metadata via push/pop context stack.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Verifies that the loop_metadata push/pop context stack correctly
//! auto-applies modified_vars and guard to LoopInvariant obligations
//! collected while a loop context is active.
//!
//! Part of #2502 (loop invariant inference for range loops).
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests invoke ay verification through `VerificationContext::verify()`.

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::VerifyResult;

mod common;

/// Auto-inferred loop metadata applies modified_vars and guard to invariant.
///
/// Simulates the proc-macro fold pass output:
/// 1. push_loop_context (modified_vars=["i"], guard="i < n")
/// 2. collect LoopInvariant obligation
/// 3. pop_loop_context
///
/// The invariant `n > 0` should use frame condition (not havoc-all) because
/// `n` is NOT in the modified_vars set.
#[test]
fn test_auto_inferred_metadata_enables_frame_condition() {
    common::with_clean_verification(|| {
        // Declare variables via thread-local path
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Precondition: n > 0
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_positive".to_string(),
            "n > 0".to_string(),
            None,
        );

        // Simulate proc-macro generated push_loop_context
        trust_vc_core::loop_metadata::push_loop_context(vec!["i".to_string()], "i < n".to_string());

        // Collect invariant while loop context is active
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::LoopInvariant,
            "invariant_n_positive".to_string(),
            "n > 0".to_string(),
            None,
        );

        // Pop context
        trust_vc_core::loop_metadata::pop_loop_context();

        // Take the context to verify
        let ctx = trust_vc_core::verify_macro::take_context().unwrap();

        // Verify that modified_vars were auto-applied
        assert_eq!(
            ctx.loop_modified_vars().get("invariant_n_positive"),
            Some(&vec!["i".to_string()]),
            "modified_vars should be auto-applied from loop context"
        );
        assert_eq!(
            ctx.loop_guards().get("invariant_n_positive"),
            Some(&"i < n".to_string()),
            "loop guard should be auto-applied from loop context"
        );

        // Verify with the context directly
        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Invariant on unmodified var with auto-inferred frame condition should verify, got: {:?}",
            result
        );
    })
}

/// Without loop context, same invariant fails (havoc-all fallback).
///
/// Control case: without push_loop_context, the invariant `n > 0`
/// has no modified_vars → havoc-all mode → counterexample.
#[test]
fn test_no_loop_context_falls_back_to_havoc_all() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());

        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_positive".to_string(),
            "n > 0".to_string(),
            None,
        );

        // No push_loop_context — direct obligation collection
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::LoopInvariant,
            "invariant_n_positive".to_string(),
            "n > 0".to_string(),
            None,
        );

        let ctx = trust_vc_core::verify_macro::take_context().unwrap();

        // No modified_vars should be set
        assert!(
            ctx.loop_modified_vars().is_empty(),
            "Without loop context, no modified_vars should be set"
        );

        // Havoc-all fallback: n > 0 is not universally valid
        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Without loop context, havoc-all should reject non-tautological invariant, got: {:?}",
            result
        );
    })
}

/// Auto-inferred metadata includes body-modified vars in modified set.
///
/// Simulates `for i in 0..n { sum += i; }` where both `i` and `sum` are
/// modified. `n` is NOT modified → frame condition preserves `n > 0`.
#[test]
fn test_auto_inferred_metadata_includes_body_modified_vars() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("sum".to_string(), "i32".to_string());

        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_positive".to_string(),
            "n > 0".to_string(),
            None,
        );

        // Simulate: for i in 0..n with body modifying sum
        trust_vc_core::loop_metadata::push_loop_context(
            vec!["i".to_string(), "sum".to_string()],
            "i < n".to_string(),
        );

        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::LoopInvariant,
            "invariant_n_unchanged".to_string(),
            "n > 0".to_string(),
            None,
        );

        trust_vc_core::loop_metadata::pop_loop_context();

        let ctx = trust_vc_core::verify_macro::take_context().unwrap();

        // Verify modified_vars includes both i and sum
        let modified = ctx
            .loop_modified_vars()
            .get("invariant_n_unchanged")
            .unwrap();
        assert!(modified.contains(&"i".to_string()));
        assert!(modified.contains(&"sum".to_string()));
        assert!(!modified.contains(&"n".to_string()));

        // n is NOT modified → frame condition preserves n > 0 → Verified
        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Invariant on unmodified var n with body-modified sum should verify, got: {:?}",
            result
        );
    })
}

/// Multiple invariants in the same loop scope all get metadata.
#[test]
fn test_multiple_invariants_share_loop_context() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("m".to_string(), "i32".to_string());

        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_pos".to_string(),
            "n > 0".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "m_pos".to_string(),
            "m > 0".to_string(),
            None,
        );

        trust_vc_core::loop_metadata::push_loop_context(vec!["i".to_string()], "i < n".to_string());

        // Two invariants in the same loop
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::LoopInvariant,
            "inv_n".to_string(),
            "n > 0".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::LoopInvariant,
            "inv_m".to_string(),
            "m > 0".to_string(),
            None,
        );

        trust_vc_core::loop_metadata::pop_loop_context();

        let ctx = trust_vc_core::verify_macro::take_context().unwrap();

        // Both invariants should have modified_vars applied
        assert!(
            ctx.loop_modified_vars().contains_key("inv_n"),
            "first invariant should have modified_vars"
        );
        assert!(
            ctx.loop_modified_vars().contains_key("inv_m"),
            "second invariant should have modified_vars"
        );

        // Both should verify (n and m are unmodified)
        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Both invariants on unmodified vars should verify, got: {:?}",
            result
        );
    })
}

/// Clear all thread locals resets loop context stack.
#[test]
fn test_clear_thread_locals_clears_loop_context() {
    common::with_clean_verification(|| {
        // Push a context
        trust_vc_core::loop_metadata::push_loop_context(
            vec!["x".to_string()],
            "x < 10".to_string(),
        );

        // Clear everything
        trust_vc_core::verify_macro::clear_all_thread_locals();

        // Now collect a LoopInvariant — should NOT get auto-applied metadata
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::LoopInvariant,
            "inv_x".to_string(),
            "x >= 0".to_string(),
            None,
        );

        let ctx = trust_vc_core::verify_macro::take_context().unwrap();
        assert!(
            ctx.loop_modified_vars().is_empty(),
            "After clear_all_thread_locals, loop context should be empty"
        );
    })
}

/// Post-loop exit fact (PostLoopAssume) is available to subsequent assertions.
///
/// Simulates `for i in 0..n` where `n == 5`:
/// 1. Invariant `n == 5` (on unmodified var, passes inductive step)
/// 2. Exit fact `i == n` (PostLoopAssume, bypasses pre-state rewriting)
/// 3. Post-loop assertion `i == 5` (requires exit fact + invariant)
///
/// Without PostLoopAssume, the exit fact gets pre-state-rewritten and loses
/// its current-state meaning, making the assertion unprovable.
#[test]
fn test_post_loop_exit_fact_enables_derived_assertion() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Precondition: n == 5
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_is_5".to_string(),
            "n == 5".to_string(),
            None,
        );

        // Loop scope: only i is modified
        trust_vc_core::loop_metadata::push_loop_context(vec!["i".to_string()], "i < n".to_string());

        // Auto-generated range bound invariant: 0 <= i
        // (This is about the modified var i — it holds trivially in
        // the inductive step for non-negative domains, but for i32 it
        // would fail. We use n == 5 instead, which is about unmodified n.)
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::LoopInvariant,
            "invariant_n_5".to_string(),
            "n == 5".to_string(),
            None,
        );

        trust_vc_core::loop_metadata::pop_loop_context();

        // Post-loop exit fact: i == n (PostLoopAssume — current state)
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::PostLoopAssume,
            "auto_loop_exit".to_string(),
            "i == n".to_string(),
            None,
        );

        // Post-loop assertion: i == 5 (from i == n AND n == 5)
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assert,
            "post_loop_i_eq_5".to_string(),
            "i == 5".to_string(),
            None,
        );

        let ctx = trust_vc_core::verify_macro::take_context().unwrap();
        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Post-loop assertion using exit fact i==n and invariant n==5 should verify, got: {:?}",
            result
        );
    })
}

/// LoopContextGuard RAII pattern prevents stale context leaks on panic.
///
/// Before #2523, push_loop_context / pop_loop_context had no RAII guard —
/// a panic between push and pop leaked a stale entry. LoopContextGuard
/// (matching QuantifierBoundVarGuard, BroadcastGuard, ContextGuard) fixes
/// this by popping in its Drop impl.
///
/// Part of #2523 (Phase 2 P5).
#[test]
fn test_loop_context_guard_cleans_up_on_panic() {
    // Phase 1: create guard + panic (guard is dropped during unwind)
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        trust_vc_core::verify_macro::clear_all_thread_locals();

        let _guard = trust_vc_core::loop_metadata::LoopContextGuard::new(
            vec!["i".to_string()],
            "i < n".to_string(),
        );
        panic!("simulated loop body panic");
        // _guard.drop() runs during unwind → pop_loop_context()
    }));
    assert!(result.is_err(), "should have caught the panic");

    // Phase 2: collect a LoopInvariant WITHOUT any loop context.
    // With RAII guard, the stale entry should have been cleaned up.
    trust_vc_core::verify_macro::collect_variable("x".to_string(), "u32".to_string());
    trust_vc_core::verify_macro::collect_obligation(
        ObligationKind::LoopInvariant,
        "post_panic_victim".to_string(),
        "x > 0".to_string(),
        None,
    );

    let ctx = trust_vc_core::verify_macro::take_context()
        .expect("context should exist after obligation collection");

    // FIXED: LoopContextGuard Drop cleaned up the stale context.
    assert!(
        !ctx.loop_modified_vars().contains_key("post_panic_victim"),
        "LoopContextGuard should have cleaned up stale context on panic — \
         victim obligation should NOT inherit dead loop's modified_vars"
    );

    trust_vc_core::verify_macro::clear_all_thread_locals();
}

/// Negative control: same scenario but exit fact as regular Assume
/// (gets pre-state-rewritten, losing post-loop semantics).
#[test]
fn test_regular_assume_exit_fact_fails_in_post_loop() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());

        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_is_5".to_string(),
            "n == 5".to_string(),
            None,
        );

        trust_vc_core::loop_metadata::push_loop_context(vec!["i".to_string()], "i < n".to_string());

        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::LoopInvariant,
            "invariant_n_5".to_string(),
            "n == 5".to_string(),
            None,
        );

        trust_vc_core::loop_metadata::pop_loop_context();

        // Same exit fact but as regular Assume (will be pre-state-rewritten)
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "exit_as_assume".to_string(),
            "i == n".to_string(),
            None,
        );

        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assert,
            "post_loop_i_eq_5".to_string(),
            "i == 5".to_string(),
            None,
        );

        let ctx = trust_vc_core::verify_macro::take_context().unwrap();
        let result = ctx.verify();
        // Regular Assume gets pre-state-rewritten: i__pre == n__pre.
        // Current-state i is unconstrained → assertion fails.
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Regular Assume exit fact should fail post-loop (pre-state rewritten), got: {:?}",
            result
        );
    })
}

/// While loop metadata: guard + modified vars applied to user invariant.
///
/// Simulates `while x < n { x += 1; }` where the user writes `invariant!(n > 0)`.
/// With loop context, `n` is NOT in modified_vars → frame condition preserves `n > 0`.
///
/// Part of #2523 (Phase 2 P3).
#[test]
fn test_while_loop_metadata_enables_frame_condition() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());

        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_positive".to_string(),
            "n > 0".to_string(),
            None,
        );

        // Simulate while-loop metadata: guard="x < n", modified_vars=["x"]
        let _guard = trust_vc_core::loop_metadata::LoopContextGuard::new(
            vec!["x".to_string()],
            "x < n".to_string(),
        );

        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::LoopInvariant,
            "invariant_n_pos".to_string(),
            "n > 0".to_string(),
            None,
        );

        drop(_guard);

        let ctx = trust_vc_core::verify_macro::take_context().unwrap();

        assert_eq!(
            ctx.loop_modified_vars().get("invariant_n_pos"),
            Some(&vec!["x".to_string()]),
            "while loop modified_vars should be auto-applied"
        );
        assert_eq!(
            ctx.loop_guards().get("invariant_n_pos"),
            Some(&"x < n".to_string()),
            "while loop guard should be auto-applied"
        );

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Invariant on unmodified var with while-loop frame condition should verify, got: {:?}",
            result
        );
    })
}

/// Nested loops: inner loop context takes precedence for its invariants.
///
/// Simulates:
/// ```
/// for i in 0..n {
///     invariant!(n > 0);  // outer loop: modified_vars=["i"]
///     for j in 0..m {
///         invariant!(m > 0);  // inner loop: modified_vars=["j"]
///     }
/// }
/// ```
///
/// Part of #2523 (Phase 2 P4).
#[test]
fn test_nested_loop_contexts_scope_correctly() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("j".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("m".to_string(), "i32".to_string());

        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "n_pos".to_string(),
            "n > 0".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::Assume,
            "m_pos".to_string(),
            "m > 0".to_string(),
            None,
        );

        // Outer loop: modified_vars=["i"]
        let _outer_guard = trust_vc_core::loop_metadata::LoopContextGuard::new(
            vec!["i".to_string()],
            "i < n".to_string(),
        );

        trust_vc_core::verify_macro::collect_obligation(
            ObligationKind::LoopInvariant,
            "outer_inv".to_string(),
            "n > 0".to_string(),
            None,
        );

        // Inner loop: modified_vars=["j"]
        {
            let _inner_guard = trust_vc_core::loop_metadata::LoopContextGuard::new(
                vec!["j".to_string()],
                "j < m".to_string(),
            );

            trust_vc_core::verify_macro::collect_obligation(
                ObligationKind::LoopInvariant,
                "inner_inv".to_string(),
                "m > 0".to_string(),
                None,
            );
        } // inner guard drops here

        drop(_outer_guard);

        let ctx = trust_vc_core::verify_macro::take_context().unwrap();

        // Outer invariant should have outer loop's modified_vars
        assert_eq!(
            ctx.loop_modified_vars().get("outer_inv"),
            Some(&vec!["i".to_string()]),
            "outer invariant should have outer loop modified_vars"
        );

        // Inner invariant should have inner loop's modified_vars (stack top)
        assert_eq!(
            ctx.loop_modified_vars().get("inner_inv"),
            Some(&vec!["j".to_string()]),
            "inner invariant should have inner loop modified_vars"
        );

        // Both should verify (n and m are unmodified in their respective scopes)
        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "Nested loop invariants on unmodified vars should verify, got: {:?}",
            result
        );
    })
}
