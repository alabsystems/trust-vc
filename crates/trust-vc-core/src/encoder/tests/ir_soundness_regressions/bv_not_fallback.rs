//! #2174 regression: BV NOT must not silently fall back to boolean NOT.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Before the fix, `encode_not` tried `try_bvnot` and on failure silently
//! applied boolean `not`. This masked sort mismatches: if a bitvector term
//! had the wrong sort due to upstream bugs, the error was swallowed and
//! boolean semantics were applied to what should be a bitvector operation.
//!
//! After the fix, `encode_not` uses `term_widths` metadata to decide:
//! - BV term (has width metadata) → `try_bvnot`, errors propagated
//! - Boolean term (no width metadata) → boolean `not`

use super::*;

/// CONTROL: boolean NOT on a boolean expression must succeed.
/// This verifies the "no width metadata → boolean NOT" path.
/// Not discriminating for #2174 — pre-fix code also succeeds here
/// because boolean NOT is the fallback the bug silently used.
#[test]
fn test_2174_boolean_not_on_compare_succeeds() {
    let mut env = QuantifierTestEnv::new();
    let x = env.solver.declare_const("x", Sort::bitvec(32));
    env.variables.insert("x".to_string(), x);
    env.var_types
        .insert("x".to_string(), TrustVcType::Int { width: 32 });

    let mut parser = env.parser();
    let expr = TrustVcExpr::Not(Box::new(TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 32 },
        }),
    }));
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2174: boolean NOT on comparison should succeed: {:?}",
        result.err()
    );
}

/// DISCRIMINATING: BV NOT on a bitvector variable must succeed and
/// propagate width metadata to the result.
#[test]
fn test_2174_bv_not_on_integer_var_succeeds_with_metadata() {
    let mut env = QuantifierTestEnv::new();
    let x = env.solver.declare_const("x", Sort::bitvec(8));
    env.variables.insert("x".to_string(), x);
    env.var_types
        .insert("x".to_string(), TrustVcType::Uint { width: 8 });

    let mut parser = env.parser();
    let expr = TrustVcExpr::Not(Box::new(TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Uint { width: 8 },
    }));
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2174: BV NOT on u8 variable should succeed: {:?}",
        result.err()
    );

    let term = result.unwrap();
    let width_info = parser.term_widths.get(&term).copied();
    assert_eq!(
        width_info,
        Some((8, false)),
        "#2174: BV NOT result must carry u8 width metadata, got: {:?}",
        width_info
    );
}

/// CONTROL: NOT on a boolean literal must use boolean NOT,
/// not attempt bitvector NOT (which would fail on Bool sort).
/// Not discriminating for #2174 — pre-fix code also succeeds here.
#[test]
fn test_2174_not_on_bool_literal_uses_boolean_not() {
    let mut env = QuantifierTestEnv::new();
    let mut parser = env.parser();
    let expr = TrustVcExpr::Not(Box::new(TrustVcExpr::BoolLit(true)));
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2174: NOT on bool literal should succeed: {:?}",
        result.err()
    );
}

/// DISCRIMINATING: When a term has BV width metadata but its actual
/// solver sort is wrong (Bool instead of BV), `encode_not` must produce
/// an error, not silently apply boolean NOT.
///
/// This is the core AC #3 test. Pre-fix, this would silently succeed
/// with boolean NOT semantics instead of propagating the sort mismatch.
#[test]
fn test_2174_bv_sort_mismatch_produces_error_not_silent_fallback() {
    let mut env = QuantifierTestEnv::new();

    // Declare `y` as Bool in the solver, but register it with BV width
    // metadata. This simulates an upstream encoding bug where a bitvector
    // variable has the wrong sort.
    let y = env.solver.declare_const("y", Sort::Bool);
    env.variables.insert("y".to_string(), y);
    env.var_types
        .insert("y".to_string(), TrustVcType::Uint { width: 8 });

    let mut parser = env.parser();
    // Manually inject BV width metadata for y (simulating the upstream bug).
    parser.term_widths.insert(y, (8, false));

    let expr = TrustVcExpr::Not(Box::new(TrustVcExpr::Var {
        name: "y".to_string(),
        ty: TrustVcType::Uint { width: 8 },
    }));
    let result = parser.encode_trust_vc_expr(&expr);

    // Post-fix: should produce an error because try_bvnot fails on Bool
    // sort, and term_widths metadata says it's BV so boolean fallback
    // is NOT used.
    assert!(
        result.is_err(),
        "#2174 SOUNDNESS: BV NOT on Bool-sort term with BV metadata \
         should error, not silently fall back to boolean NOT. Got: {:?}",
        result.ok()
    );
    let err = result.unwrap_err().to_string();
    assert!(
        err.contains("BV NOT failed"),
        "#2174: Error message should mention 'BV NOT failed', got: {}",
        err
    );
}

/// CONTROL: NOT in int_mode must use boolean NOT regardless
/// of the inner expression type (quantifier bodies use Sort::Int).
/// Not discriminating for #2174 — pre-fix code also succeeds here
/// because int_mode comparisons produce Bool sort, triggering boolean NOT.
#[test]
fn test_2174_not_in_int_mode_uses_boolean_not() {
    let mut env = QuantifierTestEnv::new();
    let mut parser = env.parser();

    // Encode NOT inside a forall quantifier (int_mode active).
    // `forall x: u32. !(x == 0)` — the NOT should use boolean NOT
    // since int_mode means all variables are Sort::Int.
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Uint { width: 32 })],
        body: Box::new(TrustVcExpr::Not(Box::new(TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Uint { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Uint { width: 32 },
            }),
        }))),
        triggers: None,
        trigger_inference_mode: None,
    };
    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "#2174: NOT in quantifier (int_mode) should succeed: {:?}",
        result.err()
    );
}
