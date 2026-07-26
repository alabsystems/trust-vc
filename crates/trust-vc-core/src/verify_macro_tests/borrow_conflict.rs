//! Borrow conflict and silent-default rejection tests.
//!
//! Tests that ProofSession borrow conflicts produce loud panics or graceful
//! skips instead of silently losing verification data (#1669, #1712,
//! #1714, #1716, #1723, #2481).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;
use crate::context_management::with_clean_thread_locals;

// === Silent i32 default rejection tests (fixes #1669) ===

#[test]
fn test_collect_variable_from_ref_skips_on_undeclared_ref() {
    with_clean_thread_locals(|| {
        collect_variable_from_ref("target_var".to_string(), "source_var".to_string());
        let ctx = get_context();
        let has_target = ctx
            .as_ref()
            .map(|c| c.get_variable_type("target_var").is_some())
            .unwrap_or(false);
        assert!(
            !has_target,
            "target_var should not be declared when source_var is missing (#2480)"
        );
    });
}

#[test]
fn test_collect_variable_from_ref_succeeds_when_ref_declared() {
    with_clean_thread_locals(|| {
        collect_variable("source_var".to_string(), "u64".to_string());
        collect_variable_from_ref("target_var".to_string(), "source_var".to_string());
        let ctx = get_context().expect("context should exist");
        assert_eq!(ctx.variables.len(), 2);
        let target = ctx.variables.iter().find(|v| v.name == "target_var");
        assert!(target.is_some(), "target_var should be declared");
        assert_eq!(
            target.unwrap().ty,
            crate::ir::TrustVcType::Uint { width: 64 },
            "target_var must inherit u64 from source_var, not default to i32"
        );
    });
}

#[test]
fn test_collect_old_value_skips_on_undeclared_variable() {
    with_clean_thread_locals(|| {
        collect_old_value("x".to_string());
        let ctx = get_context();
        let has_old = ctx
            .as_ref()
            .map(|c| c.get_variable_type("__trust_vc_old_x").is_some())
            .unwrap_or(false);
        assert!(
            !has_old,
            "__trust_vc_old_x should not be declared when x is missing (#2480)"
        );
    });
}

#[test]
fn test_collect_old_value_succeeds_when_variable_declared() {
    with_clean_thread_locals(|| {
        track_local_variable("x".to_string(), "u64".to_string());
        collect_old_value("x".to_string());
        let ctx = get_context().expect("context should exist");
        let old_var = ctx.variables.iter().find(|v| v.name == "__trust_vc_old_x");
        assert!(old_var.is_some(), "__trust_vc_old_x should be declared");
        assert_eq!(
            old_var.unwrap().ty,
            crate::ir::TrustVcType::Uint { width: 64 },
            "__trust_vc_old_x must inherit u64 from x, not default to i32"
        );
    });
}

#[test]
fn test_infer_measure_type_skips_on_undeclared_measure_variable() {
    with_clean_thread_locals(|| {
        collect_loop_decreases_measure(
            "undeclared_n".to_string(),
            Some("test_infer_measure".to_string()),
        );
        let ctx = get_context();
        let has_entry = ctx
            .as_ref()
            .map(|c| c.variables.iter().any(|v| v.name.contains("entry")))
            .unwrap_or(false);
        assert!(
            !has_entry,
            "undeclared measure should not create entry variables"
        );
    });
}

#[test]
fn test_infer_measure_type_resolves_declared_variable() {
    with_clean_thread_locals(|| {
        collect_variable("n".to_string(), "u64".to_string());
        collect_loop_decreases_measure("n".to_string(), Some("test_correct_type".to_string()));
        let ctx = get_context().expect("context should exist");
        let entry = ctx.variables.iter().find(|v| v.name == "n_entry");
        assert!(entry.is_some(), "n_entry should be declared");
        assert_eq!(
            entry.unwrap().ty,
            crate::ir::TrustVcType::Uint { width: 64 },
            "n_entry must inherit u64 from n, not default to i32"
        );
    });
}

#[test]
fn test_infer_measure_type_skips_on_undeclared_expression_variables() {
    with_clean_thread_locals(|| {
        collect_loop_decreases_measure(
            "a - b".to_string(),
            Some("test_expr_undeclared".to_string()),
        );
        let ctx = get_context();
        let has_entry = ctx
            .as_ref()
            .map(|c| c.variables.iter().any(|v| v.name.contains("entry")))
            .unwrap_or(false);
        assert!(
            !has_entry,
            "undeclared expression should not create entry variables"
        );
    });
}

#[test]
fn test_infer_measure_type_resolves_expression_variable() {
    with_clean_thread_locals(|| {
        collect_variable("n".to_string(), "u64".to_string());
        collect_loop_decreases_measure("n - i".to_string(), Some("test_expr_partial".to_string()));
        let ctx = get_context().expect("context should exist");
        let entry = ctx.variables.iter().find(|v| v.name == "n_minus_i_entry");
        assert!(entry.is_some(), "n_minus_i_entry should be declared");
        assert_eq!(
            entry.unwrap().ty,
            crate::ir::TrustVcType::Uint { width: 64 },
            "n_minus_i_entry must inherit u64 from n (first matching variable)"
        );
    });
}

// --- Session-level borrow conflict regression tests (#1716, #1714, #1712, #2481) ---
//
// With ProofSession consolidation (#2481), a single RefCell guards all four
// fields (context, in_proof_mode, local_var_types, assert_by_scope_stack).
// Borrowing the session blocks all fields simultaneously.

/// restore_context skips when ProofSession is borrowed (#1955, #2481).
#[test]
fn test_restore_context_skips_on_borrow_conflict() {
    with_clean_thread_locals(|| {
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            restore_context(None); // should skip, not panic
        });
    });
}

/// take_context returns None when ProofSession is borrowed (#1955, #2481).
#[test]
fn test_take_context_skips_on_borrow_conflict() {
    with_clean_thread_locals(|| {
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            let result = take_context();
            assert!(result.is_none());
        });
    });
}

#[test]
#[should_panic(expected = "CRITICAL: get_context")]
fn test_get_context_panics_on_borrow_conflict() {
    with_clean_thread_locals(|| {
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            let _ = get_context();
        });
    });
}

#[test]
fn test_verify_collected_reports_borrow_conflict_as_error() {
    with_clean_thread_locals(|| {
        collect_obligation(
            crate::vc::ObligationKind::Assert,
            "borrowed_verify".to_string(),
            "true".to_string(),
            None,
        );
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            let result = verify_collected();
            assert!(
                matches!(result, crate::encoder::VerifyResult::Error { ref message } if message.contains("verification context is already borrowed")),
                "borrowed context must surface as VerifyResult::Error, got: {:?}",
                result
            );
        });
    });
}

/// clear_context gracefully skips when ProofSession is borrowed (#1955, #2481).
#[test]
fn test_clear_context_skips_on_borrow_conflict() {
    with_clean_thread_locals(|| {
        collect_obligation(
            crate::vc::ObligationKind::Assert,
            "test".to_string(),
            "true".to_string(),
            None,
        );
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            clear_context(); // should skip, not panic
        });
    });
}

/// begin_assert_by_scope skips when ProofSession is borrowed (#1955, #2481).
#[test]
fn test_begin_assert_by_scope_skips_on_session_borrow_conflict() {
    with_clean_thread_locals(|| {
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            begin_assert_by_scope("test_scope".to_string()); // should skip, not panic
        });
    });
}

/// track_local_variable skips when ProofSession is borrowed (#1955, #2481).
#[test]
fn test_track_local_variable_skips_on_borrow_conflict() {
    with_clean_thread_locals(|| {
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            track_local_variable("x".to_string(), "u64".to_string()); // should skip, not panic
        });
    });
}

// --- translate_rust_to_smt regression tests (#1723) ---

#[test]
#[should_panic(expected = "is not valid Rust syntax")]
fn test_translate_rust_to_smt_panics_on_parse_failure() {
    with_clean_thread_locals(|| {
        super::super::translate_rust_to_smt(">>> not valid rust <<<");
    });
}

#[test]
fn test_translate_rust_to_smt_allows_unsupported_expr_fallback() {
    with_clean_thread_locals(|| {
        let result = super::super::translate_rust_to_smt("x as i64");
        assert_eq!(result, "x as i64");
    });
}

#[test]
fn test_translate_rust_to_smt_translates_supported_exprs() {
    with_clean_thread_locals(|| {
        let result = super::super::translate_rust_to_smt("x > 0");
        assert_eq!(result, "(x > 0)");
    });
}

#[test]
fn test_translate_rust_to_smt_falls_back_on_session_borrow_conflict() {
    with_clean_thread_locals(|| {
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            let result = super::super::translate_rust_to_smt("x > 0");
            assert_eq!(result, "x > 0");
        });
    });
}

// --- Remaining session borrow regression tests (#1716, #2481) ---

/// end_assert_by_scope skips when ProofSession is borrowed (#1955, #2481).
#[test]
fn test_end_assert_by_scope_skips_on_session_borrow_conflict() {
    with_clean_thread_locals(|| {
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            super::super::end_assert_by_scope("x > 0".to_string(), Some("test.rs:1".to_string()));
        });
    });
}

/// collect_old_value gracefully skips when ProofSession is borrowed (#1955, #2481).
#[test]
fn test_collect_old_value_skips_on_session_borrow_conflict() {
    with_clean_thread_locals(|| {
        collect_variable("x".to_string(), "u64".to_string());
        track_local_variable("x".to_string(), "u64".to_string());
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            collect_old_value("x".to_string()); // should skip, not panic
        });
    });
}

/// collect_old_value gracefully skips when ProofSession is borrowed
/// and variable was previously registered (#2480, #2481).
#[test]
fn test_collect_old_value_skips_when_session_borrowed() {
    with_clean_thread_locals(|| {
        collect_variable("x".to_string(), "u64".to_string());
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            collect_old_value("x".to_string());
        });
    });
}

// --- Graceful cleanup skip tests (#1955, #2481) ---

/// clear_all_thread_locals completes when ProofSession is borrowed (#1955, #2481).
#[test]
fn test_clear_all_thread_locals_skips_on_session_borrow() {
    with_clean_thread_locals(|| {
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            clear_all_thread_locals(); // should complete without panicking
        });
    });
}

/// clear_all_thread_locals completes when BROADCAST_LEMMAS is borrowed (#1955).
#[test]
fn test_clear_all_thread_locals_skips_on_broadcast_lemmas_borrow() {
    with_clean_thread_locals(|| {
        crate::broadcast_state::test_helpers::with_broadcast_lemmas_borrowed(|| {
            clear_all_thread_locals();
        });
    });
}

/// clear_all_thread_locals completes when BROADCAST_PARAMS is borrowed (#1955).
#[test]
fn test_clear_all_thread_locals_skips_on_broadcast_params_borrow() {
    with_clean_thread_locals(|| {
        crate::broadcast_state::test_helpers::with_broadcast_params_borrowed(|| {
            clear_all_thread_locals();
        });
    });
}

/// clear_all_thread_locals completes when TRIGGER_PATTERNS is borrowed (#1955).
#[test]
fn test_clear_all_thread_locals_skips_on_trigger_patterns_borrow() {
    with_clean_thread_locals(|| {
        crate::broadcast_state::test_helpers::with_trigger_patterns_borrowed(|| {
            clear_all_thread_locals();
        });
    });
}

/// clear_all_thread_locals completes when EXTERN_SPEC_CONTRACTS is borrowed (#1955).
#[test]
fn test_clear_all_thread_locals_skips_on_extern_spec_contracts_borrow() {
    with_clean_thread_locals(|| {
        crate::extern_spec_verify::test_helpers::with_extern_spec_contracts_borrowed(|| {
            clear_all_thread_locals();
        });
    });
}

// --- Broadcast data-path graceful skip tests (#1955) ---

#[test]
fn test_set_broadcast_mode_skips_on_params_borrow() {
    with_clean_thread_locals(|| {
        crate::broadcast_state::test_helpers::with_broadcast_params_borrowed(|| {
            set_broadcast_mode(true);
        });
        set_broadcast_mode(false);
    });
}

#[test]
fn test_register_trigger_skips_on_borrow() {
    with_clean_thread_locals(|| {
        crate::broadcast_state::test_helpers::with_trigger_patterns_borrowed(|| {
            register_trigger(0, "test_pattern".to_string());
        });
    });
}

#[test]
fn test_track_broadcast_param_skips_on_borrow() {
    with_clean_thread_locals(|| {
        crate::broadcast_state::test_helpers::with_broadcast_params_borrowed(|| {
            crate::broadcast_state::track_broadcast_param("test_param".to_string());
        });
    });
}

#[test]
fn test_register_broadcast_lemma_skips_on_lemmas_borrow() {
    with_clean_thread_locals(|| {
        crate::broadcast_state::test_helpers::with_broadcast_lemmas_borrowed(|| {
            register_broadcast_lemma("test_lemma".to_string());
        });
    });
}
