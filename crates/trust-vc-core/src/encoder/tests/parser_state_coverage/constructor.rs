//! Constructor, lifecycle, and mode detection tests for AstExpressionParser.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Sort;
use std::collections::HashMap;

use super::make_solver;
use crate::encoder::parser_state::AstExpressionParser;
use crate::ir::{DatatypeVariant, TrustVcType};

fn counter_datatype_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "Counter".to_string(),
        variants: vec![DatatypeVariant::new(
            "Counter",
            vec![("count".to_string(), TrustVcType::MathInt)],
        )],
    }
}

// --- int_mode detection ---

#[test]
fn test_int_mode_false_when_bv_variables_exist() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let x = solver.bv_var("x", 32);
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    assert!(
        !parser.int_mode(),
        "int_mode should be false when BV variables exist"
    );
    assert!(
        !parser.use_int_arithmetic,
        "use_int_arithmetic should be false when BV variables exist"
    );
}

#[test]
fn test_int_mode_true_when_all_int_variables() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let n = solver.int_var("n");
    variables.insert("n".to_string(), n);
    var_types.insert("n".to_string(), crate::ir::TrustVcType::MathInt);

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    assert!(
        parser.int_mode(),
        "int_mode should be true when all variables are Sort::Int"
    );
    assert!(
        parser.use_int_arithmetic,
        "use_int_arithmetic should be true when no BV variables"
    );
}

#[test]
fn test_int_mode_true_when_mathint_mixed_with_datatype() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let n = solver.int_var("n");
    variables.insert("n".to_string(), n);
    var_types.insert("n".to_string(), TrustVcType::MathInt);

    let counter = solver.int_var("counter");
    variables.insert("counter".to_string(), counter);
    var_types.insert("counter".to_string(), counter_datatype_ty());

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    assert!(
        parser.int_mode(),
        "Datatype companions should not disable int_mode when MathInt variables are present"
    );
    assert!(
        parser.use_int_arithmetic,
        "MathInt + Datatype should keep use_int_arithmetic enabled"
    );
}

#[test]
fn test_int_mode_true_when_mathint_mixed_with_bool() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let n = solver.int_var("n");
    variables.insert("n".to_string(), n);
    var_types.insert("n".to_string(), TrustVcType::MathInt);

    let flag = solver.bool_var("flag");
    variables.insert("flag".to_string(), flag);
    var_types.insert("flag".to_string(), TrustVcType::Bool);

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    assert!(
        parser.int_mode(),
        "Bool companions should not disable int_mode when MathInt variables are present"
    );
    assert!(
        parser.use_int_arithmetic,
        "MathInt + Bool should keep use_int_arithmetic enabled"
    );
}

#[test]
fn test_int_mode_false_when_only_bool_variables() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let flag = solver.bool_var("flag");
    variables.insert("flag".to_string(), flag);
    var_types.insert("flag".to_string(), TrustVcType::Bool);

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    assert!(
        !parser.int_mode(),
        "bool-only sessions should not opt into scalar Int mode"
    );
    assert!(
        !parser.use_int_arithmetic,
        "bool-only sessions should leave use_int_arithmetic disabled"
    );
}

#[test]
fn test_int_mode_false_when_only_float_variables() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), TrustVcType::Float { width: 32 });

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    assert!(
        !parser.int_mode(),
        "float-only sessions should not opt into scalar Int mode"
    );
    assert!(
        !parser.use_int_arithmetic,
        "float-only sessions should leave use_int_arithmetic disabled"
    );
}

#[test]
fn test_int_mode_false_when_float_mixed_with_mathint() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let n = solver.int_var("n");
    variables.insert("n".to_string(), n);
    var_types.insert("n".to_string(), TrustVcType::MathInt);

    let x = solver.declare_const("x", Sort::FloatingPoint(8, 24));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), TrustVcType::Float { width: 32 });

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    assert!(
        !parser.int_mode(),
        "float presence should disable scalar Int mode even when MathInt variables exist"
    );
    assert!(
        !parser.use_int_arithmetic,
        "float presence should keep use_int_arithmetic disabled"
    );
}

#[test]
fn test_int_mode_false_when_no_variables() {
    let mut solver = make_solver();
    let variables = HashMap::new();
    let var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    assert!(
        !parser.int_mode(),
        "int_mode should be false when no variables declared"
    );
    assert!(
        !parser.use_int_arithmetic,
        "use_int_arithmetic requires non-empty variables map"
    );
}

#[test]
fn test_quantifier_depth_controls_int_mode() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let x = solver.bv_var("x", 32);
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    assert!(!parser.int_mode(), "depth 0 with BV vars -> not int_mode");
    parser.quantifier_depth = 1;
    assert!(
        parser.int_mode(),
        "depth 1 -> int_mode regardless of BV vars"
    );
    parser.quantifier_depth = 0;
    assert!(!parser.int_mode(), "back to depth 0 -> not int_mode");
}

// --- term_widths pre-population ---

#[test]
fn test_term_widths_prepopulated_from_bv_variables() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let x = solver.bv_var("x", 32);
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });

    let y = solver.bv_var("y", 64);
    variables.insert("y".to_string(), y);
    var_types.insert("y".to_string(), crate::ir::TrustVcType::Uint { width: 64 });

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    assert_eq!(
        parser.term_widths.get(&x),
        Some(&(32, true)),
        "i32 variable should be tracked as (32, signed=true)"
    );
    assert_eq!(
        parser.term_widths.get(&y),
        Some(&(64, false)),
        "u64 variable should be tracked as (64, signed=false)"
    );
}

#[test]
fn test_term_widths_excludes_bool_and_mathint() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let b = solver.bool_var("b");
    variables.insert("b".to_string(), b);
    var_types.insert("b".to_string(), crate::ir::TrustVcType::Bool);

    let n = solver.int_var("n");
    variables.insert("n".to_string(), n);
    var_types.insert("n".to_string(), crate::ir::TrustVcType::MathInt);

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    assert!(
        !parser.term_widths.contains_key(&b),
        "Bool variables should not appear in term_widths"
    );
    assert!(
        !parser.term_widths.contains_key(&n),
        "MathInt variables should not appear in term_widths"
    );
}

#[test]
fn test_collection_lengths_tracked_as_pointer_width_unsigned() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let pw = crate::ir::pointer_width();
    let s = solver.declare_const("s", Sort::array(Sort::bitvec(pw), Sort::bitvec(32)));
    variables.insert("s".to_string(), s);
    var_types.insert(
        "s".to_string(),
        crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    );

    let s_len = solver.bv_var("s_len", pw);
    collection_lengths.insert("s".to_string(), s_len);

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    assert_eq!(
        parser.term_widths.get(&s_len),
        Some(&(pw, false)),
        "Collection length should be tracked as (pointer_width, unsigned)"
    );
}

// --- overflow mode ---

#[test]
fn test_overflow_checking_mode() {
    let mut solver = make_solver();
    let variables = HashMap::new();
    let var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let parser_no_overflow = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    assert!(
        !parser_no_overflow.overflow_behavior.should_check(),
        "default should not check overflow"
    );

    let parser_overflow = AstExpressionParser::with_overflow_checking(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
        true,
    );
    assert!(
        parser_overflow.overflow_behavior.should_check(),
        "explicit true should enable overflow checking"
    );
}
