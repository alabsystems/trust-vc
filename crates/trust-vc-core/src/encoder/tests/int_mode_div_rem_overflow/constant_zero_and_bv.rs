//! Constant-zero rejection and BV-mode signed div/rem overflow checks.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from int_mode_div_rem_overflow.rs (#2145).

use super::*;

#[test]
fn test_ir_division_by_constant_zero_rejected() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let x = solver.declare_const("x", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    let mut parser = make_parser(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = signed_div_expr(signed_var("x"), signed_lit(0));
    let err = parser
        .encode_trust_vc_expr(&expr)
        .expect_err("x / 0 must be rejected on ir_encoder path");
    assert!(
        err.to_string().contains("Division by zero"),
        "Expected division-by-zero error, got: {}",
        err
    );
}

#[test]
fn test_ir_remainder_by_constant_zero_rejected() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let x = solver.declare_const("x", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    var_types.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    let mut parser = make_parser(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = signed_rem_expr(signed_var("x"), signed_lit(0));
    let err = parser
        .encode_trust_vc_expr(&expr)
        .expect_err("x % 0 must be rejected on ir_encoder path");
    assert!(
        err.to_string().contains("Modulo by zero"),
        "Expected modulo-by-zero error, got: {}",
        err
    );
}

#[test]
fn test_ir_signed_bv_division_emits_div0_and_overflow_checks() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let y = solver.declare_const("y", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    var_types.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    var_types.insert("y".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    let mut parser = make_parser_with_overflow(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = signed_div_expr(signed_var("x"), signed_var("y"));
    parser
        .encode_trust_vc_expr(&expr)
        .expect("x / y should encode when divisor is non-literal");
    let checks = parser.take_overflow_checks();
    assert!(
        checks.iter().any(|(name, _)| name == "division by zero"),
        "Expected runtime division-by-zero guard in BV mode"
    );
    assert!(
        checks
            .iter()
            .any(|(name, _)| name == "signed division overflow"),
        "Expected signed MIN/-1 overflow guard in BV mode"
    );
}

#[test]
fn test_ir_signed_bv_remainder_emits_div0_and_overflow_checks() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let y = solver.declare_const("y", Sort::bitvec(32));
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    var_types.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    var_types.insert("y".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    let mut parser = make_parser_with_overflow(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = signed_rem_expr(signed_var("x"), signed_var("y"));
    parser
        .encode_trust_vc_expr(&expr)
        .expect("x % y should encode when divisor is non-literal");
    let checks = parser.take_overflow_checks();
    assert!(
        checks.iter().any(|(name, _)| name == "division by zero"),
        "Expected runtime modulo-by-zero guard in BV mode"
    );
    assert!(
        checks
            .iter()
            .any(|(name, _)| name == "signed remainder overflow"),
        "Expected signed MIN/-1 overflow guard for remainder in BV mode"
    );
}
