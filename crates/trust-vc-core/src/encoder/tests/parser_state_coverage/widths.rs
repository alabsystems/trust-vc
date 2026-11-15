//! Width inference and BV coercion tests for AstExpressionParser.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use super::make_solver;
use crate::encoder::parser_state::AstExpressionParser;

#[test]
fn test_infer_int_width_with_mixed_types() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let x = solver.bv_var("x", 32);
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });

    let y = solver.bv_var("y", 32);
    variables.insert("y".to_string(), y);
    var_types.insert("y".to_string(), crate::ir::TrustVcType::Uint { width: 32 });

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    assert_eq!(
        parser.infer_int_width(),
        32,
        "two i32/u32 variables should infer width 32"
    );
}

#[test]
fn test_infer_int_width_fallback_to_32() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let b = solver.bool_var("b");
    variables.insert("b".to_string(), b);
    var_types.insert("b".to_string(), crate::ir::TrustVcType::Bool);

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    assert_eq!(
        parser.infer_int_width(),
        32,
        "no integer types should fall back to 32"
    );
}

// --- BV coercion ---

#[test]
fn test_coerce_bv_widths_refuses_two_widths_met_untyped() {
    let mut solver = make_solver();
    let narrow = solver.bv_var("narrow", 8);
    let wide = solver.bv_var("wide", 32);

    let variables = HashMap::new();
    let var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    parser.term_widths.insert(narrow, (8, false));
    parser.term_widths.insert(wide, (32, true));

    // Neither term's own type is known here: a `term_widths` sign is the
    // hash-consed term's, not the value's, so nothing is widened — two
    // widths are refused (design-trust-proof-backend.md §5b rule 10).
    assert!(
        parser.coerce_bv_widths(narrow, wide).is_err(),
        "terms of two widths met untyped must be refused, never widened"
    );
}

#[test]
fn test_coerce_bv_widths_equal_widths_unchanged() {
    let mut solver = make_solver();
    let a_term = solver.bv_var("a", 32);
    let b_term = solver.bv_var("b", 32);

    let variables = HashMap::new();
    let var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    parser.term_widths.insert(a_term, (32, true));
    parser.term_widths.insert(b_term, (32, false));

    let (a, b) = parser
        .coerce_bv_widths(a_term, b_term)
        .expect("coercion should succeed");

    assert_eq!(a, a_term, "equal-width terms should be unchanged");
    assert_eq!(b, b_term, "equal-width terms should be unchanged");
}
