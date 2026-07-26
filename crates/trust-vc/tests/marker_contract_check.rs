// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Marker contract verification tests for trust_vc proc-macros.
//!
//! These tests verify that trust_vc proc-macros emit the markers defined in
//! the internal metadata-contract notes. The tests compile code that uses the macros
//! and verify runtime behavior, while the marker emission is verified by:
//! 1. Source code inspection (markers are visible in crates/trust_vc/src/lib.rs)
// 2. These tests confirm the macros work as documented
//
// Marker verification matrix (trust_vc crate):
//
// | Macro | Marker(s) | Test |
// |-------|-----------|------|
// | old! | __trust_vc_old_marker | test_old_marker |
// | decreases_to! | __trust_vc_decreases_to_lhs_rhs | test_decreases_to_marker |
// | assert_by! | __trust_vc_assert_by_scope, __trust_vc_assert_by_content | test_assert_by_marker |
// | assert_by_nonlinear! | __trust_vc_solver_mode, __trust_vc_assert_expr | test_solver_mode_nonlinear |
// | assert_by_bit_vector! | __trust_vc_solver_mode, __trust_vc_assert_expr | test_solver_mode_bitvector |
// | assert_by_compute! | __trust_vc_solver_mode, __trust_vc_assert_expr | test_solver_mode_compute |
// | invariant! | __trust_vc_loop_invariant | test_loop_invariant_marker |
// | loop_decreases! | __trust_vc_loop_decreases, __trust_vc_loop_measure | test_loop_decreases_marker |

use trust_vc::{
    assert_by, assert_by_bit_vector, assert_by_compute, assert_by_nonlinear, decreases_to,
    invariant, loop_decreases, old,
};

mod common;

// ============================================================================
// Old Marker (Contract: Old category)
// Emits: __trust_vc_old_marker
// ============================================================================

#[test]
fn test_old_marker() {
    // old! captures pre-state value
    // Marker: __trust_vc_old_marker (line 819 in lib.rs)
    let x = 42;
    let captured = old!(x);
    assert_eq!(captured, 42);
}

// test_old_marker_with_expression removed: old!(a + b) was unsound passthrough (#1836).
// Complex expressions in old!() now correctly produce a compile error.

// ============================================================================
// Decreases-to Marker (Contract: Decreases Relation category)
// Emits: __trust_vc_decreases_to_lhs_rhs
// ============================================================================

#[test]
fn test_decreases_to_marker() {
    // decreases_to! checks lexicographic decrease
    // Marker: __trust_vc_decreases_to_lhs_rhs (line 875 in lib.rs)
    // At runtime, returns true (verification happens at compile time)
    let result = decreases_to!(8i64 => 4i64);
    assert!(result);
}

#[test]
fn test_decreases_to_lexicographic() {
    // Lexicographic decrease: first equal, second decreases
    let result = decreases_to!(10i64, 8i64 => 10i64, 4i64);
    assert!(result);
}

// ============================================================================
// Assert-by Markers (Contract: Assert By category)
// Emits: __trust_vc_assert_by_scope, __trust_vc_assert_by_content
// ============================================================================

#[test]
fn test_assert_by_marker() {
    // assert_by! creates scoped assertion
    // Markers: __trust_vc_assert_by_scope (line 951)
    //          __trust_vc_assert_by_content (line 958)
    let x = 5;
    assert_by! { x > 0 };
}

#[test]
fn test_assert_by_with_proof_steps() {
    let a = 3;
    let b = 4;
    assert_by! {
        let sum = a + b;
        sum == 7
    };
}

// ============================================================================
// Solver Mode Markers (Contract: Solver Mode category)
// Emits: __trust_vc_solver_mode, __trust_vc_assert_expr
// ============================================================================

#[test]
fn test_solver_mode_nonlinear() {
    // assert_by_nonlinear! uses nonlinear arithmetic solver
    // Markers: __trust_vc_solver_mode = "nonlinear_arith" (line 1015)
    //          __trust_vc_assert_expr (line 1016)
    let x = 3;
    assert_by_nonlinear!(x * x == 9);
}

#[test]
fn test_solver_mode_bitvector() {
    // assert_by_bit_vector! uses bitvector solver
    // Markers: __trust_vc_solver_mode = "bit_vector" (line 1067)
    //          __trust_vc_assert_expr (line 1068)
    let x: u32 = 0xFF;
    assert_by_bit_vector!(x & 0x0F == 0x0F);
}

#[test]
fn test_solver_mode_compute() {
    // assert_by_compute! uses symbolic evaluation
    // Markers: __trust_vc_solver_mode = "compute" (line 1127)
    //          __trust_vc_assert_expr (line 1128)
    let x = 2;
    let y = 3;
    assert_by_compute!(x + y == 5);
}

#[test]
fn test_solver_mode_compute_block_lets_compile() {
    let outer = 2;
    assert_by_compute!({
        let x = outer;
        let y = x + 3;
        y == 5
    });
}

// ============================================================================
// Loop Invariant Marker (Contract: Loop category)
// Emits: __trust_vc_loop_invariant
// ============================================================================

#[test]
fn test_loop_invariant_marker() {
    // invariant! specifies loop invariant
    // Marker: __trust_vc_loop_invariant (line 1205)
    let mut i = 0;
    while i < 5 {
        invariant!(i >= 0);
        i += 1;
    }
}

#[test]
fn test_loop_invariant_multiple() {
    let mut i = 0;
    let n = 10;
    while i < n {
        invariant!(i >= 0);
        invariant!(i <= n);
        i += 1;
    }
}

// ============================================================================
// Loop Decreases Markers (Contract: Loop category - termination)
// Emits: __trust_vc_loop_decreases, __trust_vc_loop_measure
// ============================================================================

#[test]
fn test_loop_decreases_marker() {
    // loop_decreases! specifies termination measure
    // Markers: __trust_vc_loop_decreases (line 1275)
    //          __trust_vc_loop_measure (line 1277)
    // Must register variables in VerificationContext because cfg(test)
    // path calls collect_loop_decreases_measure → infer_measure_type (#1669).
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i64".to_string());
        let mut n: i64 = 5;
        while n > 0 {
            loop_decreases!(n);
            n -= 1;
        }
    });
}

#[test]
fn test_loop_decreases_lexicographic() {
    // Lexicographic termination measure
    // Register variables for infer_measure_type (#1669).
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("outer".to_string(), "i64".to_string());
        trust_vc_core::verify_macro::collect_variable("inner".to_string(), "i64".to_string());
        let mut outer: i64 = 3;
        let mut inner: i64;
        while outer > 0 {
            inner = 3;
            while inner > 0 {
                loop_decreases!((outer, inner));
                inner -= 1;
            }
            outer -= 1;
        }
    });
}

// ============================================================================
// Combined usage tests
// ============================================================================

#[test]
fn test_invariant_and_decreases_combined() {
    // Both markers emitted in same loop
    // Register variables for infer_measure_type (#1669).
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i64".to_string());
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i64".to_string());
        let mut i: i64 = 0;
        let n: i64 = 5;
        while i < n {
            invariant!(i >= 0 && i <= n);
            loop_decreases!(n - i);
            i += 1;
        }
    });
}

#[test]
fn test_old_in_postcondition_context() {
    // Simulate postcondition pattern with old!
    let mut x = 10;
    let pre_x = old!(x);
    x += 5;
    assert_eq!(pre_x + 5, x);
}
