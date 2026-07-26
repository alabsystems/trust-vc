//! Int-mode div/rem overflow checks and width-correct div-by-zero
//! check tests (#2028).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from int_mode_div_rem_overflow.rs (#2145).

use super::*;
use ay_dpll::api::TermKind;

/// At quantifier_depth > 0, div overflow checks are suppressed because the
/// predicates reference bound variables that are free at the outer scope.
/// Part of #2557: same guard as add/sub/mul/neg.
#[test]
fn test_ir_int_mode_division_emits_div0_and_min_neg1_checks() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    var_types.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    var_types.insert("y".to_string(), crate::ir::TrustVcType::Int { width: 32 });

    // At quantifier_depth == 0 (int mode via use_int_arithmetic):
    // div-by-zero overflow check IS emitted. (Signed MIN/-1 check
    // requires wrap_ctx which is None under use_int_arithmetic.)
    {
        let mut parser = make_parser_with_overflow(
            &mut solver,
            &variables,
            &mut collection_lengths,
            &var_types,
            &functions,
        );
        parser.use_int_arithmetic = true;
        let expr = signed_div_expr(signed_var("x"), signed_var("y"));
        parser
            .encode_trust_vc_expr(&expr)
            .expect("Int-mode x / y should encode at depth 0");
        let checks = parser.take_overflow_checks();
        assert!(
            checks.iter().any(|(name, _)| name == "division by zero"),
            "Expected Int-mode runtime division-by-zero guard at depth 0"
        );
    }

    // At quantifier_depth == 1: overflow checks are SUPPRESSED (#2557).
    {
        let mut parser = make_parser_with_overflow(
            &mut solver,
            &variables,
            &mut collection_lengths,
            &var_types,
            &functions,
        );
        parser.quantifier_depth = 1;
        parser.push_quantifier_scope(&[
            ("x".to_string(), crate::ir::TrustVcType::Int { width: 32 }),
            ("y".to_string(), crate::ir::TrustVcType::Int { width: 32 }),
        ]);
        let expr = signed_div_expr(signed_var("x"), signed_var("y"));
        parser
            .encode_trust_vc_expr(&expr)
            .expect("Int-mode x / y should encode at depth 1");
        let checks = parser.take_overflow_checks();
        assert!(
            checks.is_empty(),
            "Overflow checks should be suppressed at quantifier_depth > 0 (#2557), got: {:?}",
            checks.iter().map(|(n, _)| n).collect::<Vec<_>>()
        );
    }
}

/// At quantifier_depth > 0, rem overflow checks are suppressed (#2557).
#[test]
fn test_ir_int_mode_remainder_emits_div0_and_min_neg1_checks() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    var_types.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    var_types.insert("y".to_string(), crate::ir::TrustVcType::Int { width: 32 });

    // At quantifier_depth == 0 (int mode via use_int_arithmetic):
    // mod-by-zero overflow check IS emitted. (Signed MIN/-1 check
    // requires wrap_ctx which is None under use_int_arithmetic.)
    {
        let mut parser = make_parser_with_overflow(
            &mut solver,
            &variables,
            &mut collection_lengths,
            &var_types,
            &functions,
        );
        parser.use_int_arithmetic = true;
        let expr = signed_rem_expr(signed_var("x"), signed_var("y"));
        parser
            .encode_trust_vc_expr(&expr)
            .expect("Int-mode x % y should encode at depth 0");
        let checks = parser.take_overflow_checks();
        assert!(
            checks.iter().any(|(name, _)| name == "modulo by zero"),
            "Expected Int-mode runtime modulo-by-zero guard at depth 0"
        );
    }

    // At quantifier_depth == 1: overflow checks are SUPPRESSED (#2557).
    {
        let mut parser = make_parser_with_overflow(
            &mut solver,
            &variables,
            &mut collection_lengths,
            &var_types,
            &functions,
        );
        parser.quantifier_depth = 1;
        parser.push_quantifier_scope(&[
            ("x".to_string(), crate::ir::TrustVcType::Int { width: 32 }),
            ("y".to_string(), crate::ir::TrustVcType::Int { width: 32 }),
        ]);
        let expr = signed_rem_expr(signed_var("x"), signed_var("y"));
        parser
            .encode_trust_vc_expr(&expr)
            .expect("Int-mode x % y should encode at depth 1");
        let checks = parser.take_overflow_checks();
        assert!(
            checks.is_empty(),
            "Overflow checks should be suppressed at quantifier_depth > 0 (#2557), got: {:?}",
            checks.iter().map(|(n, _)| n).collect::<Vec<_>>()
        );
    }
}

/// At quantifier_depth > 0, signed MIN/-1 division should become undefined
/// even without `with_overflow_checks()`, because Rust always panics on this
/// pair (#1873).
#[test]
fn test_ir_int_mode_division_min_neg1_in_quantifier_encodes_undefined_guard() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    var_types.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    var_types.insert("y".to_string(), crate::ir::TrustVcType::Int { width: 32 });

    let mut parser = make_parser(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&[
        ("x".to_string(), crate::ir::TrustVcType::Int { width: 32 }),
        ("y".to_string(), crate::ir::TrustVcType::Int { width: 32 }),
    ]);

    let expr = signed_div_expr(signed_var("x"), signed_var("y"));
    let result = parser
        .encode_trust_vc_expr(&expr)
        .expect("Int-mode x / y should encode at depth 1");
    assert!(
        parser.take_overflow_checks().is_empty(),
        "depth>0 division should not leak outer-scope overflow predicates"
    );

    let children = parser.solver.term_children(result);
    assert!(
        matches!(parser.solver.term_kind(result), TermKind::Ite),
        "division guard should encode as ite(cond, fresh, result), got {:?}",
        parser.solver.term_kind(result)
    );
    assert_eq!(children.len(), 3, "ite should have cond/then/else children");
    assert!(
        matches!(
            parser.solver.term_kind(children[1]),
            TermKind::Var { ref name } if name.starts_with("__int_div_min_panic")
        ),
        "then-branch should be the fresh MIN/-1 panic variable, got {:?}",
        parser.solver.term_kind(children[1])
    );
    assert!(
        !matches!(
            parser.solver.term_kind(children[2]),
            TermKind::Var { ref name } if name.starts_with("__int_div_min_panic")
        ),
        "else-branch should remain the normal division result"
    );
}

/// At quantifier_depth > 0, signed MIN/-1 remainder should also become
/// undefined instead of leaking an outer-scope overflow predicate (#1873).
#[test]
fn test_ir_int_mode_remainder_min_neg1_in_quantifier_encodes_undefined_guard() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
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
    parser.quantifier_depth = 1;
    parser.push_quantifier_scope(&[
        ("x".to_string(), crate::ir::TrustVcType::Int { width: 32 }),
        ("y".to_string(), crate::ir::TrustVcType::Int { width: 32 }),
    ]);

    let expr = signed_rem_expr(signed_var("x"), signed_var("y"));
    let result = parser
        .encode_trust_vc_expr(&expr)
        .expect("Int-mode x % y should encode at depth 1");
    assert!(
        parser.take_overflow_checks().is_empty(),
        "depth>0 remainder should not leak outer-scope overflow predicates"
    );

    let children = parser.solver.term_children(result);
    assert!(
        matches!(parser.solver.term_kind(result), TermKind::Ite),
        "remainder guard should encode as ite(cond, fresh, result), got {:?}",
        parser.solver.term_kind(result)
    );
    assert_eq!(children.len(), 3, "ite should have cond/then/else children");
    assert!(
        matches!(
            parser.solver.term_kind(children[1]),
            TermKind::Var { ref name } if name.starts_with("__int_rem_min_panic")
        ),
        "then-branch should be the fresh MIN/-1 panic variable, got {:?}",
        parser.solver.term_kind(children[1])
    );
    assert!(
        !matches!(
            parser.solver.term_kind(children[2]),
            TermKind::Var { ref name } if name.starts_with("__int_rem_min_panic")
        ),
        "else-branch should remain the normal remainder result"
    );
}

// ========================================================================
// Width-correct div-by-zero check tests (#2028)
// ========================================================================

/// Division of u8 variables must emit an 8-bit div-by-zero check,
/// not a default-width 32-bit check that would cause a sort mismatch.
#[test]
fn test_ir_div_by_zero_check_u8_width() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Uint { width: 8 };
    let x = solver.declare_const("x", Sort::bitvec(8));
    let y = solver.declare_const("y", Sort::bitvec(8));
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    var_types.insert("x".to_string(), ty.clone());
    var_types.insert("y".to_string(), ty.clone());

    let mut parser = make_parser_with_overflow(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = typed_div_expr(typed_var("x", ty.clone()), typed_var("y", ty.clone()), ty);
    parser
        .encode_trust_vc_expr(&expr)
        .expect("u8 division should encode without sort mismatch (#2028)");

    let checks = parser.take_overflow_checks();
    assert!(
        checks.iter().any(|(name, _)| name == "division by zero"),
        "Expected div-by-zero guard for u8 division"
    );
}

/// Division of u64 variables must emit a 64-bit div-by-zero check.
#[test]
fn test_ir_div_by_zero_check_u64_width() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Uint { width: 64 };
    let x = solver.declare_const("x", Sort::bitvec(64));
    let y = solver.declare_const("y", Sort::bitvec(64));
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    var_types.insert("x".to_string(), ty.clone());
    var_types.insert("y".to_string(), ty.clone());

    let mut parser = make_parser_with_overflow(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = typed_div_expr(typed_var("x", ty.clone()), typed_var("y", ty.clone()), ty);
    parser
        .encode_trust_vc_expr(&expr)
        .expect("u64 division should encode without sort mismatch (#2028)");

    let checks = parser.take_overflow_checks();
    assert!(
        checks.iter().any(|(name, _)| name == "division by zero"),
        "Expected div-by-zero guard for u64 division"
    );
}

/// Remainder of i8 variables must emit an 8-bit mod-by-zero check.
#[test]
fn test_ir_rem_by_zero_check_i8_width() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Int { width: 8 };
    let x = solver.declare_const("x", Sort::bitvec(8));
    let y = solver.declare_const("y", Sort::bitvec(8));
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    var_types.insert("x".to_string(), ty.clone());
    var_types.insert("y".to_string(), ty.clone());

    let mut parser = make_parser_with_overflow(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = typed_rem_expr(typed_var("x", ty.clone()), typed_var("y", ty.clone()), ty);
    parser
        .encode_trust_vc_expr(&expr)
        .expect("i8 remainder should encode without sort mismatch (#2028)");

    let checks = parser.take_overflow_checks();
    assert!(
        checks.iter().any(|(name, _)| name == "division by zero"),
        "Expected div-by-zero guard for i8 remainder"
    );
}

/// i64 remainder must produce a 64-bit mod-by-zero check plus signed overflow.
#[test]
fn test_ir_rem_by_zero_check_i64_width() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let ty = crate::ir::TrustVcType::Int { width: 64 };
    let x = solver.declare_const("x", Sort::bitvec(64));
    let y = solver.declare_const("y", Sort::bitvec(64));
    variables.insert("x".to_string(), x);
    variables.insert("y".to_string(), y);
    var_types.insert("x".to_string(), ty.clone());
    var_types.insert("y".to_string(), ty.clone());

    let mut parser = make_parser_with_overflow(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = typed_rem_expr(typed_var("x", ty.clone()), typed_var("y", ty.clone()), ty);
    parser
        .encode_trust_vc_expr(&expr)
        .expect("i64 remainder should encode without sort mismatch (#2028)");

    let checks = parser.take_overflow_checks();
    assert!(
        checks.iter().any(|(name, _)| name == "division by zero"),
        "Expected div-by-zero guard for i64 remainder"
    );
    assert!(
        checks
            .iter()
            .any(|(name, _)| name == "signed remainder overflow"),
        "Expected signed MIN/-1 overflow guard for i64 remainder"
    );
}
