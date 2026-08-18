//! Direct cast/match residual regressions for #2371.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

fn encode_i32_match(expr: &TrustVcExpr) -> (Solver, Term, Term) {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let x = solver.declare_const("x", Sort::bitvec(32));
    let mut variables = std::collections::HashMap::new();
    variables.insert("x".into(), x);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("x".into(), i32_ty());
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.term_widths.insert(x, (32, true));
    let match_term = parser
        .encode_trust_vc_expr(expr)
        .expect("match expression should encode");
    drop(parser);

    (solver, x, match_term)
}

fn encode_bool_cast_bv(to_ty: TrustVcType) -> (Solver, Term, Term, (u32, bool)) {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let b = solver.declare_const("b", Sort::Bool);
    let mut variables = std::collections::HashMap::new();
    variables.insert("b".into(), b);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("b".into(), TrustVcType::Bool);
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let expr = TrustVcExpr::Cast {
        expr: Box::new(bool_var("b")),
        from_ty: TrustVcType::Bool,
        to_ty: to_ty.clone(),
    };

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    // A bool-only environment defaults to use_int_arithmetic=true because no
    // BV widths are registered yet. Force BV mode so this test actually hits
    // cast_bool_to_int's bitvector branch.
    parser.use_int_arithmetic = false;
    let cast_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("bool-to-int cast should encode in BV mode");
    let width_info = parser.term_widths[&cast_term];
    drop(parser);

    (solver, b, cast_term, width_info)
}

fn encode_bool_cast_int_mode(to_ty: TrustVcType) -> (Solver, Term, Term) {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let b = solver.declare_const("b", Sort::Bool);
    let mut variables = std::collections::HashMap::new();
    variables.insert("b".into(), b);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("b".into(), TrustVcType::Bool);
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let expr = TrustVcExpr::Cast {
        expr: Box::new(bool_var("b")),
        from_ty: TrustVcType::Bool,
        to_ty,
    };

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.quantifier_depth = 1;
    let cast_term = parser
        .encode_trust_vc_expr(&expr)
        .expect("bool-to-int cast should encode in int mode");
    drop(parser);

    (solver, b, cast_term)
}

fn assert_bv_match_mapping(
    solver: &mut Solver,
    scrutinee: Term,
    match_term: Term,
    input: i64,
    expected: i64,
    label: &str,
) {
    solver.try_push().unwrap();
    let input_term = solver.try_bv_const(input, 32).unwrap();
    let expected_term = solver.try_bv_const(expected, 32).unwrap();
    let is_input = solver.try_eq(scrutinee, input_term).unwrap();
    let is_expected = solver.try_eq(match_term, expected_term).unwrap();
    let not_expected = solver.try_not(is_expected).unwrap();
    solver.try_assert_term(is_input).unwrap();
    solver.try_assert_term(not_expected).unwrap();
    let sat = solver.try_check_sat().unwrap();
    solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "{label}: solver found counterexample {:?}",
        sat
    );
}

fn assert_bool_cast_bv_value(
    solver: &mut Solver,
    bool_term: Term,
    cast_term: Term,
    when_true: bool,
    expected: i64,
    width: u32,
    label: &str,
) {
    solver.try_push().unwrap();
    let condition = if when_true {
        bool_term
    } else {
        solver.try_not(bool_term).unwrap()
    };
    let expected_term = solver.try_bv_const(expected, width).unwrap();
    let is_expected = solver.try_eq(cast_term, expected_term).unwrap();
    let not_expected = solver.try_not(is_expected).unwrap();
    solver.try_assert_term(condition).unwrap();
    solver.try_assert_term(not_expected).unwrap();
    let sat = solver.try_check_sat().unwrap();
    solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "{label}: solver found counterexample {:?}",
        sat
    );
}

fn assert_bool_cast_int_value(
    solver: &mut Solver,
    bool_term: Term,
    cast_term: Term,
    when_true: bool,
    expected: i64,
    label: &str,
) {
    solver.try_push().unwrap();
    let condition = if when_true {
        bool_term
    } else {
        solver.try_not(bool_term).unwrap()
    };
    let expected_term = solver.int_const(expected);
    let is_expected = solver.try_eq(cast_term, expected_term).unwrap();
    let not_expected = solver.try_not(is_expected).unwrap();
    solver.try_assert_term(condition).unwrap();
    solver.try_assert_term(not_expected).unwrap();
    let sat = solver.try_check_sat().unwrap();
    solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "{label}: solver found counterexample {:?}",
        sat
    );
}

#[test]
fn test_match_pattern_or_fold_preserves_each_literal_branch() {
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(i32_var("x")),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Or(vec![
                    MatchPattern::Lit(i32_lit(1)),
                    MatchPattern::Lit(i32_lit(3)),
                    MatchPattern::Lit(i32_lit(5)),
                ]),
                body: i32_lit(10),
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Wildcard,
                body: i32_lit(20),
                guard: None,
            },
        ],
        ty: i32_ty(),
    };

    let (mut solver, x, match_term) = encode_i32_match(&expr);
    assert_bv_match_mapping(&mut solver, x, match_term, 1, 10, "x=1 should take OR arm");
    assert_bv_match_mapping(&mut solver, x, match_term, 3, 10, "x=3 should take OR arm");
    assert_bv_match_mapping(&mut solver, x, match_term, 5, 10, "x=5 should take OR arm");
    assert_bv_match_mapping(
        &mut solver,
        x,
        match_term,
        2,
        20,
        "x=2 should take wildcard fallback",
    );
}

#[test]
fn test_match_pattern_or_with_wildcard_becomes_default_arm() {
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(i32_var("x")),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Lit(i32_lit(1)),
                body: i32_lit(20),
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Or(vec![
                    MatchPattern::Lit(i32_lit(1)),
                    MatchPattern::Wildcard,
                ]),
                body: i32_lit(10),
                guard: None,
            },
        ],
        ty: i32_ty(),
    };

    let (mut solver, x, match_term) = encode_i32_match(&expr);
    assert_bv_match_mapping(
        &mut solver,
        x,
        match_term,
        1,
        20,
        "earlier literal arm should still win for x=1",
    );
    assert_bv_match_mapping(
        &mut solver,
        x,
        match_term,
        2,
        10,
        "wildcard inside OR should make the final arm unconditional",
    );
}

#[test]
fn test_match_pattern_empty_or_behaves_like_default_arm() {
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(i32_var("x")),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Lit(i32_lit(2)),
                body: i32_lit(20),
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Or(vec![]),
                body: i32_lit(10),
                guard: None,
            },
        ],
        ty: i32_ty(),
    };

    let (mut solver, x, match_term) = encode_i32_match(&expr);
    assert_bv_match_mapping(
        &mut solver,
        x,
        match_term,
        2,
        20,
        "earlier literal arm should still override the empty-OR default",
    );
    assert_bv_match_mapping(
        &mut solver,
        x,
        match_term,
        7,
        10,
        "empty OR should act like the wildcard default for non-matching inputs",
    );
}

#[test]
fn test_cast_bool_to_int_bv_mode_uses_bitvector_zero_one_and_registers_width() {
    let (mut solver, b, cast_term, width_info) =
        encode_bool_cast_bv(TrustVcType::Uint { width: 8 });

    assert_eq!(
        width_info,
        (8, false),
        "BV bool-to-u8 cast should register the result as an unsigned 8-bit term",
    );

    assert_bool_cast_bv_value(
        &mut solver,
        b,
        cast_term,
        true,
        1,
        8,
        "true should cast to BV one",
    );
    assert_bool_cast_bv_value(
        &mut solver,
        b,
        cast_term,
        false,
        0,
        8,
        "false should cast to BV zero",
    );
}

#[test]
fn test_cast_bool_to_int_int_mode_uses_int_zero_one() {
    let (mut solver, b, cast_term) = encode_bool_cast_int_mode(TrustVcType::Int { width: 32 });

    assert_bool_cast_int_value(
        &mut solver,
        b,
        cast_term,
        true,
        1,
        "true should cast to Int one in int mode",
    );
    assert_bool_cast_int_value(
        &mut solver,
        b,
        cast_term,
        false,
        0,
        "false should cast to Int zero in int mode",
    );
}

// ========================================================================
// #2505 Slice 4: Or-pattern constructor bindings
// ========================================================================

use crate::ir::DatatypeVariant;

fn two_variant_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "TV".into(),
        variants: vec![
            DatatypeVariant::new("Foo", vec![("_0".into(), TrustVcType::Int { width: 32 })]),
            DatatypeVariant::new("Bar", vec![("_0".into(), TrustVcType::Int { width: 32 })]),
        ],
    }
}

fn tv_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.into(),
        ty: two_variant_ty(),
    }
}

/// Encode a match over a two-variant datatype scrutinee. Returns the solver,
/// the scrutinee term, and the match result term.
fn encode_tv_match(expr: &TrustVcExpr) -> (AYEncoder, Term, Term) {
    // Register the datatype through the production encoder before declaring the
    // scrutinee. Final ay authenticates every native tester/selector handle and
    // correctly rejects forged `FuncDecl::new(...)` handles, so this fixture
    // must exercise the same native declarations as production.
    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            name: "e".into(),
            ty: two_variant_ty(),
            bounded_len: false,
        })
        .expect("native TV variable should register its datatype");
    let e = encoder.variables["e"];
    let term = encoder
        .encode_condition_typed(expr)
        .expect("match expression should encode without error");

    (encoder, e, term)
}

/// DISCRIMINATING: `match e { Foo(x) | Bar(x) => x }` should encode
/// without error. Pre-fix: Or-pattern returned `Ok(vec![])` for bindings,
/// so `x` was "Undefined variable" during body encoding.
#[test]
fn test_or_pattern_constructor_binding_encodes_without_error() {
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(tv_var("e")),
        arms: vec![MatchArm {
            pattern: MatchPattern::Or(vec![
                MatchPattern::Constructor {
                    variant_name: "Foo".into(),
                    bindings: vec!["x".into()],
                    has_rest: false,
                },
                MatchPattern::Constructor {
                    variant_name: "Bar".into(),
                    bindings: vec!["x".into()],
                    has_rest: false,
                },
            ]),
            body: TrustVcExpr::Var {
                name: "x".into(),
                ty: TrustVcType::Int { width: 32 },
            },
            guard: None,
        }],
        ty: TrustVcType::Int { width: 32 },
    };

    let (_encoder, _e, _match_term) = encode_tv_match(&expr);
    // Success: encoding didn't panic with "Undefined variable: x".
}

/// DISCRIMINATING: When is_Foo(e) holds, the match result must equal the Foo
/// selector value, and likewise for Bar. Verifies the ITE selects the correct
/// alternative's field term.
#[test]
fn test_or_pattern_constructor_binding_selects_correct_field() {
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(tv_var("e")),
        arms: vec![MatchArm {
            pattern: MatchPattern::Or(vec![
                MatchPattern::Constructor {
                    variant_name: "Foo".into(),
                    bindings: vec!["x".into()],
                    has_rest: false,
                },
                MatchPattern::Constructor {
                    variant_name: "Bar".into(),
                    bindings: vec!["x".into()],
                    has_rest: false,
                },
            ]),
            body: TrustVcExpr::Var {
                name: "x".into(),
                ty: TrustVcType::Int { width: 32 },
            },
            guard: None,
        }],
        ty: TrustVcType::Int { width: 32 },
    };

    let (mut encoder, e, match_term) = encode_tv_match(&expr);

    // When is_Foo(e), the match result should equal Foo's selector for e.
    encoder.solver.try_push().unwrap();
    let foo_cond = encoder.solver.try_datatype_tester("TV_Foo", e).unwrap();
    let foo_field = encoder
        .solver
        .try_datatype_selector("TV_Foo_0", e, Sort::bitvec(32))
        .unwrap();
    encoder.solver.try_assert_term(foo_cond).unwrap();
    let eq = encoder.solver.try_eq(match_term, foo_field).unwrap();
    let neq = encoder.solver.try_not(eq).unwrap();
    encoder.solver.try_assert_term(neq).unwrap();
    let sat = encoder.solver.check_sat();
    encoder.solver.try_pop().unwrap();
    assert!(
        sat.is_unsat(),
        "when is_Foo(e), match result should equal Foo's field, got {:?}",
        sat,
    );

    // When is_Bar(e) and NOT is_Foo(e), the match result should equal Bar's
    // selector. (The ITE defaults to Bar's term when Foo's tester is false.)
    encoder.solver.try_push().unwrap();
    let bar_cond = encoder.solver.try_datatype_tester("TV_Bar", e).unwrap();
    let foo_cond2 = encoder.solver.try_datatype_tester("TV_Foo", e).unwrap();
    let not_foo = encoder.solver.try_not(foo_cond2).unwrap();
    let bar_field = encoder
        .solver
        .try_datatype_selector("TV_Bar_0", e, Sort::bitvec(32))
        .unwrap();
    encoder.solver.try_assert_term(bar_cond).unwrap();
    encoder.solver.try_assert_term(not_foo).unwrap();
    let eq2 = encoder.solver.try_eq(match_term, bar_field).unwrap();
    let neq2 = encoder.solver.try_not(eq2).unwrap();
    encoder.solver.try_assert_term(neq2).unwrap();
    let sat2 = encoder.solver.check_sat();
    encoder.solver.try_pop().unwrap();
    assert!(
        sat2.is_unsat(),
        "when is_Bar(e) and not is_Foo(e), match result should equal Bar's field, got {:?}",
        sat2,
    );
}

/// Or-pattern bindings must not leak into outer scope after the match.
/// `(match e { Foo(x) | Bar(x) => x }) + outer_x` should use the outer
/// `outer_x` for the addition, not the pattern-bound `x`.
#[test]
fn test_or_pattern_constructor_binding_restores_outer_scope() {
    use crate::ir::ArithOp;

    let match_expr = TrustVcExpr::Match {
        scrutinee: Box::new(tv_var("e")),
        arms: vec![MatchArm {
            pattern: MatchPattern::Or(vec![
                MatchPattern::Constructor {
                    variant_name: "Foo".into(),
                    bindings: vec!["x".into()],
                    has_rest: false,
                },
                MatchPattern::Constructor {
                    variant_name: "Bar".into(),
                    bindings: vec!["x".into()],
                    has_rest: false,
                },
            ]),
            body: TrustVcExpr::Var {
                name: "x".into(),
                ty: TrustVcType::Int { width: 32 },
            },
            guard: None,
        }],
        ty: TrustVcType::Int { width: 32 },
    };

    // Wrap: (match e { ... }) + x where outer x is a separate BV variable.
    let add_expr = TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(match_expr),
        right: Box::new(TrustVcExpr::Var {
            name: "x".into(),
            ty: TrustVcType::Int { width: 32 },
        }),
        ty: TrustVcType::Int { width: 32 },
    };

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let e = solver.declare_const("e", crate::encoder::datatype::datatype_carrier_sort("TV"));
    let outer_x = solver.declare_const("x", Sort::bitvec(32));
    let mut variables = std::collections::HashMap::new();
    variables.insert("e".into(), e);
    variables.insert("x".into(), outer_x);
    let mut var_types = std::collections::HashMap::new();
    var_types.insert("e".into(), two_variant_ty());
    var_types.insert("x".into(), TrustVcType::Int { width: 32 });
    let mut collection_lengths = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    parser.term_widths.insert(outer_x, (32, true));

    let result = parser.encode_trust_vc_expr(&add_expr);
    assert!(
        result.is_ok(),
        "outer x should be accessible after Or-pattern match scope: {:?}",
        result.err(),
    );
}
