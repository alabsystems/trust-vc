//! Context lifecycle tests: proof mode, collect, clear, thread isolation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;
use crate::context_management::with_clean_thread_locals;
use crate::vc::ObligationKind;

#[test]
fn test_set_and_get_proof_mode() {
    with_clean_thread_locals(|| {
        // Test default is false
        assert!(!is_in_proof_mode());

        // Test setting to true
        set_proof_mode(true);
        assert!(is_in_proof_mode());

        // Test setting back to false
        set_proof_mode(false);
        assert!(!is_in_proof_mode());
    });
}

#[test]
fn test_collect_obligation_assert() {
    with_clean_thread_locals(|| {
        // Collect an assertion obligation
        collect_obligation(
            ObligationKind::Assert,
            "test_assert".to_string(),
            "x > 0".to_string(),
            Some("test.rs:10".to_string()),
        );

        // Verify context was created
        let ctx = get_context();
        assert!(ctx.is_some());
    });
}

#[test]
fn test_collect_obligation_assume() {
    with_clean_thread_locals(|| {
        // Collect an assumption obligation
        collect_obligation(
            ObligationKind::Assume,
            "test_assume".to_string(),
            "y < 10".to_string(),
            Some("test.rs:20".to_string()),
        );

        // Verify context was created
        let ctx = get_context();
        assert!(ctx.is_some());
    });
}

#[test]
fn test_collect_typed_obligation() {
    with_clean_thread_locals(|| {
        // Track local variables first (this is how they get into LOCAL_VAR_TYPES)
        track_local_variable("x".to_string(), "i32".to_string());
        track_local_variable("y".to_string(), "bool".to_string());

        // Collect a typed obligation (it captures local types automatically)
        collect_typed_obligation(
            ObligationKind::Assert,
            "typed_assert".to_string(),
            "x > 0 && y".to_string(),
            Some("test.rs:30".to_string()),
        );

        // Verify context was created
        let ctx = get_context();
        assert!(ctx.is_some());
    });
}

#[test]
fn test_collect_variable() {
    with_clean_thread_locals(|| {
        // Collect some variables
        collect_variable("foo".to_string(), "String".to_string());
        collect_variable("bar".to_string(), "i32".to_string());

        // Verify context was created with variables
        let ctx = get_context();
        assert!(ctx.is_some());
    });
}

#[test]
fn test_track_local_variable() {
    with_clean_thread_locals(|| {
        // Track some local variables with recognized TrustVcType types
        track_local_variable("local_x".to_string(), "u64".to_string());
        track_local_variable("local_y".to_string(), "Seq<i32>".to_string());

        // The function adds to thread-local storage
        // We can't directly inspect it but can verify it doesn't panic
    });
}

#[test]
fn test_clear_context() {
    with_clean_thread_locals(|| {
        // Add some context
        collect_obligation(
            ObligationKind::Assume,
            "test".to_string(),
            "x > 0".to_string(),
            None,
        );

        // Verify it exists
        assert!(get_context().is_some());

        // Clear it
        clear_context();

        // Verify it's gone
        assert!(get_context().is_none());
    });
}

#[test]
fn test_collect_decreases_measure() {
    with_clean_thread_locals(|| {
        // Collect a decreases measure
        collect_decreases_measure("n".to_string(), Some("test.rs:70".to_string()));

        // Verify context was created
        let ctx = get_context();
        assert!(ctx.is_some());
    });
}

#[test]
fn test_collect_decrease_obligation() {
    with_clean_thread_locals(|| {
        // Collect a decrease obligation
        collect_decrease_obligation("recursive_call", "n - 1 < n", Some("test.rs:80"));

        // Verify context was created
        let ctx = get_context();
        assert!(ctx.is_some());
    });
}

#[test]
fn test_verify_decreases() {
    with_clean_thread_locals(|| {
        // Verify decreases for a function
        verify_decreases("factorial", "n".to_string(), "n - 1".to_string());

        // Verify context was created
        let ctx = get_context();
        assert!(ctx.is_some());
    });
}

#[test]
fn test_multiple_obligations() {
    with_clean_thread_locals(|| {
        // Collect multiple obligations
        for i in 0..5 {
            collect_obligation(
                if i % 2 == 0 {
                    ObligationKind::Assume
                } else {
                    ObligationKind::Assert
                },
                format!("test_{}", i),
                format!("x_{} > 0", i),
                Some(format!("test.rs:{}", i * 10)),
            );
        }

        // Verify context exists
        let ctx = get_context();
        assert!(ctx.is_some());
    });
}

#[test]
fn test_proof_mode_with_obligations() {
    with_clean_thread_locals(|| {
        // Set proof mode
        set_proof_mode(true);
        assert!(is_in_proof_mode());

        // Collect obligations in proof mode
        collect_obligation(
            ObligationKind::Assume,
            "proof_assume".to_string(),
            "x > 0".to_string(),
            None,
        );
        collect_obligation(
            ObligationKind::Assert,
            "proof_assert".to_string(),
            "x < 100".to_string(),
            None,
        );

        // Proof mode shouldn't affect collection
        assert!(get_context().is_some());

        // Reset proof mode
        set_proof_mode(false);
        assert!(!is_in_proof_mode());
    });
}

#[test]
fn test_nested_context_skips_gracefully() {
    with_clean_thread_locals(|| {
        collect_obligation(ObligationKind::Assert, "setup".into(), "true".into(), None);
        let before = get_context().unwrap().obligations.len();

        // Nested borrow conflict: skip gracefully instead of panicking (#1955, #2481)
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            collect_obligation(
                ObligationKind::Assert,
                "nested".into(),
                "x > 0".into(),
                None,
            );
        });

        let after = get_context().unwrap().obligations.len();
        assert_eq!(
            before, after,
            "obligation should be skipped on borrow conflict"
        );
    });
}

#[test]
fn test_nested_typed_obligation_skips_gracefully() {
    with_clean_thread_locals(|| {
        collect_typed_obligation(ObligationKind::Assert, "setup".into(), "true".into(), None);
        let before = get_context().unwrap().obligations.len();

        // Nested borrow conflict on typed path: skip gracefully (#1955, #2481)
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            collect_typed_obligation(
                ObligationKind::Assert,
                "nested".into(),
                "y < 10".into(),
                None,
            );
        });

        let after = get_context().unwrap().obligations.len();
        assert_eq!(
            before, after,
            "typed obligation should be skipped on borrow conflict"
        );
    });
}

#[test]
fn test_collect_requires_ensures() {
    with_clean_thread_locals(|| {
        // Collect requires and ensures obligations
        collect_obligation(
            ObligationKind::Requires,
            "precondition".to_string(),
            "n > 0".to_string(),
            Some("test.rs:100".to_string()),
        );

        collect_obligation(
            ObligationKind::Ensures,
            "postcondition".to_string(),
            "result > 0".to_string(),
            Some("test.rs:101".to_string()),
        );

        // Verify context was created
        let ctx = get_context();
        assert!(ctx.is_some());
    });
}

#[test]
fn test_collect_measure_obligations() {
    with_clean_thread_locals(|| {
        // Collect measure-related obligations
        collect_obligation(
            ObligationKind::MeasureNonNegative,
            "measure_nonneg".to_string(),
            "n >= 0".to_string(),
            Some("test.rs:110".to_string()),
        );

        collect_obligation(
            ObligationKind::MeasureDecreases,
            "measure_decreases".to_string(),
            "n - 1 < n".to_string(),
            Some("test.rs:111".to_string()),
        );

        // Verify context was created
        let ctx = get_context();
        assert!(ctx.is_some());
    });
}

#[test]
fn test_thread_local_isolation() {
    use std::thread;

    with_clean_thread_locals(|| {
        // Add obligation in main thread
        collect_obligation(
            ObligationKind::Assert,
            "main_thread".to_string(),
            "main_var > 0".to_string(),
            None,
        );

        // Spawn new thread and verify isolation
        let handle = thread::spawn(|| {
            // Thread should start with empty context
            assert!(get_context().is_none());

            // Add obligation in spawned thread
            collect_obligation(
                ObligationKind::Assume,
                "spawned_thread".to_string(),
                "thread_var < 100".to_string(),
                None,
            );

            // Verify it was added in this thread
            assert!(get_context().is_some());
        });

        handle.join().unwrap();

        // Main thread should still have its context
        assert!(get_context().is_some());
    });
}

// --- Phase 5 dual-path: collect_obligation_expr + PRE_BUILT_EXPRS cache ---

#[test]
fn test_collect_obligation_expr_caches_and_delegates() {
    use crate::ir::TrustVcType;
    use crate::ir_expr::TrustVcExpr;
    use crate::obligation_collection::take_pre_built_expr;

    with_clean_thread_locals(|| {
        let expr = TrustVcExpr::Compare {
            op: crate::ir_expr::CompareOp::Gt,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        };

        collect_obligation_expr(
            ObligationKind::Assert,
            "gt_assert".to_string(),
            "x > 0".to_string(),
            expr.clone(),
            Some("test.rs:42".to_string()),
        );

        // Verify context was created (delegation to collect_typed_obligation)
        assert!(get_context().is_some());

        // Verify the expr was cached and can be retrieved
        let taken = take_pre_built_expr("gt_assert", "x > 0");
        assert!(
            taken.is_some(),
            "PRE_BUILT_EXPRS should contain cached expr"
        );
        assert_eq!(taken.unwrap(), expr);
    });
}

#[test]
fn test_take_pre_built_expr_removes_entry() {
    use crate::ir_expr::TrustVcExpr;
    use crate::obligation_collection::take_pre_built_expr;

    with_clean_thread_locals(|| {
        let expr = TrustVcExpr::BoolLit(true);

        collect_obligation_expr(
            ObligationKind::Assume,
            "take_test".to_string(),
            "true".to_string(),
            expr,
            None,
        );

        // First take should succeed
        let first = take_pre_built_expr("take_test", "true");
        assert!(first.is_some(), "First take should return the cached expr");

        // Second take should return None (take semantics — removed on first take)
        let second = take_pre_built_expr("take_test", "true");
        assert!(
            second.is_none(),
            "Second take should return None (entry consumed)"
        );
    });
}

#[test]
fn test_take_pre_built_expr_skips_on_session_borrow_conflict() {
    use crate::ir_expr::TrustVcExpr;
    use crate::obligation_collection::take_pre_built_expr;

    with_clean_thread_locals(|| {
        collect_obligation_expr(
            ObligationKind::Assume,
            "borrowed_take_test".to_string(),
            "true".to_string(),
            TrustVcExpr::BoolLit(true),
            None,
        );

        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            let taken = take_pre_built_expr("borrowed_take_test", "true");
            assert!(
                taken.is_none(),
                "borrow conflict should skip cache removal instead of panicking"
            );
        });

        let taken = take_pre_built_expr("borrowed_take_test", "true");
        assert!(
            taken.is_some(),
            "skip-on-conflict should leave the cached expr intact"
        );
    });
}

#[test]
fn test_clear_pre_built_exprs_empties_cache() {
    use crate::ir::TrustVcType;
    use crate::ir_expr::TrustVcExpr;
    use crate::obligation_collection::{clear_pre_built_exprs, take_pre_built_expr};

    with_clean_thread_locals(|| {
        collect_obligation_expr(
            ObligationKind::Assert,
            "clear_test".to_string(),
            "y > 0".to_string(),
            TrustVcExpr::Var {
                name: "y".to_string(),
                ty: TrustVcType::Int { width: 32 },
            },
            None,
        );

        // Clear the cache
        clear_pre_built_exprs();

        // Take should return None after clear
        let taken = take_pre_built_expr("clear_test", "y > 0");
        assert!(
            taken.is_none(),
            "Cache should be empty after clear_pre_built_exprs"
        );
    });
}

#[test]
fn test_collect_solver_mode_obligation_expr_caches() {
    use crate::ir::TrustVcType;
    use crate::ir_expr::TrustVcExpr;
    use crate::obligation_collection::take_pre_built_expr;

    with_clean_thread_locals(|| {
        let expr = TrustVcExpr::Compare {
            op: crate::ir_expr::CompareOp::Le,
            left: Box::new(TrustVcExpr::Var {
                name: "a".to_string(),
                ty: TrustVcType::Uint { width: 32 },
            }),
            right: Box::new(TrustVcExpr::Var {
                name: "b".to_string(),
                ty: TrustVcType::Uint { width: 32 },
            }),
        };

        collect_solver_mode_obligation_expr(
            ObligationKind::Assert,
            "solver_mode_test".to_string(),
            "a <= b".to_string(),
            expr.clone(),
            Some("test.rs:99".to_string()),
            "nonlinear_arith",
        );

        // Verify context was created
        assert!(get_context().is_some());

        // Verify cache
        let taken = take_pre_built_expr("solver_mode_test", "a <= b");
        assert!(taken.is_some(), "Solver mode expr should be cached");
        assert_eq!(taken.unwrap(), expr);
    });
}
